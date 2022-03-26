/**
 * Implementation of a Record Manager with several memory reclamation schemes.
 * This file provides an Allocator plugin for the Record Manager.
 * Specifically, it implements a simple bump allocator that allocates a 4MB slab
 * of memory, and then parcels it out in multiples of the cache-line size.
 * When a 4MB slab is exhausted, a new slab is allocated.
 * This allocator does not actually support freeing memory to the OS.
 * 
 * Copyright (C) 2016 Trevor Brown
 * Contact (tabrown [at] cs [dot] toronto [dot edu]) with any questions or comments.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef ALLOC_BUMP_H
#define	ALLOC_BUMP_H

#include "machineconstants.h"
#include "globals.h"
#include "allocator_interface.h"
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <vector>
using namespace std;

template<typename T = void>
class allocator_bump : public allocator_interface<T> {
    private:
        const int cachelines;    // # cachelines needed to store an object of type T
        // for bump allocation from a contiguous chunk of memory
        T ** mem;             // mem[tid*PREFETCH_SIZE_WORDS] = pointer to current array to perform bump allocation from
        int * memBytes;       // memBytes[tid*PREFETCH_SIZE_WORDS] = size of mem in bytes
        T ** current;         // current[tid*PREFETCH_SIZE_WORDS] = pointer to current position in array mem
        vector<T*> ** toFree; // toFree[tid] = pointer to vector of bump allocation arrays to free when this allocator is destroyed

        T* bump_memory_next(const int tid) {
            T* result = current[tid*PREFETCH_SIZE_WORDS];
            current[tid*PREFETCH_SIZE_WORDS] = (T*) (((char*) current[tid*PREFETCH_SIZE_WORDS]) + (cachelines*BYTES_IN_CACHELINE));
            return result;
        }
        int bump_memory_bytes_remaining(const int tid) {
            return (((char*) mem[tid*PREFETCH_SIZE_WORDS])+memBytes[tid*PREFETCH_SIZE_WORDS]) - ((char*) current[tid*PREFETCH_SIZE_WORDS]);
        }
        bool bump_memory_full(const int tid) {
            return (((char*) current[tid*PREFETCH_SIZE_WORDS])+cachelines*BYTES_IN_CACHELINE > ((char*) mem[tid*PREFETCH_SIZE_WORDS])+memBytes[tid*PREFETCH_SIZE_WORDS]);
        }
        // call this when mem is null, or doesn't contain enough space to allocate an object
        void bump_memory_allocate(const int tid) {
            mem[tid*PREFETCH_SIZE_WORDS] = (T*) malloc(1<<24);
            memBytes[tid*PREFETCH_SIZE_WORDS] = 1<<24;
            current[tid*PREFETCH_SIZE_WORDS] = mem[tid*PREFETCH_SIZE_WORDS];
            toFree[tid]->push_back(mem[tid*PREFETCH_SIZE_WORDS]); // remember we allocated this to free it later
#ifdef HAS_FUNCTION_aligned_alloc
#else
            // align on cacheline boundary
            int mod = (int) (((long) mem[tid*PREFETCH_SIZE_WORDS]) % BYTES_IN_CACHELINE);
            if (mod > 0) {
                // we are ignoring the first mod bytes of mem, because if we
                // use them, we will not be aligning objects to cache lines.
                current[tid*PREFETCH_SIZE_WORDS] = (T*) (((char*) mem[tid*PREFETCH_SIZE_WORDS]) + BYTES_IN_CACHELINE - mod);
            } else {
                current[tid*PREFETCH_SIZE_WORDS] = mem[tid*PREFETCH_SIZE_WORDS];
            }
#endif
            assert((((long) current[tid*PREFETCH_SIZE_WORDS]) % BYTES_IN_CACHELINE) == 0);
        }

    public:
        template<typename _Tp1>
        struct rebind {
            typedef allocator_bump<_Tp1> other;
        };

        // reserve space for ONE object of type T
        T* allocate(const int tid) {
            // bump-allocate from a contiguous chunk of memory
            if (!mem[tid*PREFETCH_SIZE_WORDS] || bump_memory_full(tid)) {
                bump_memory_allocate(tid);
                MEMORY_STATS {
                    this->debug->addAllocated(tid, memBytes[tid*PREFETCH_SIZE_WORDS] / cachelines / BYTES_IN_CACHELINE);
                    VERBOSE DEBUG2 {
//                        if ((this->debug->getAllocated(tid) % 2000) == 0) {
//                            this->debugInterfaces->reclaim->debugPrintStatus(tid);
//                            debugPrintStatus(tid);
                            COUTATOMICTID("allocated "<<(memBytes[tid*PREFETCH_SIZE_WORDS] / cachelines / BYTES_IN_CACHELINE)/*this->debug->getAllocated(tid)*/<<" records of size "<<sizeof(T)<<endl);
//                            COUTATOMIC(" ");
//                            this->pool->debugPrintStatus(tid);
//                            COUTATOMIC(endl);
//                        }
                    }
                }
            }
            return bump_memory_next(tid);
        }
        void static deallocate(const int tid, T * const p) {
            // no op for this allocator; memory is freed only by the destructor.
        }
        void deallocateAndClear(const int tid, blockbag<T> * const bag) {
            // the bag is cleared, which makes it seem like we're leaking memory,
            // but it will be freed in the destructor as we release the huge
            // slabs of memory.
            bag->clearWithoutFreeingElements();
        }

        void debugPrintStatus(const int tid) {}

        void initThread(const int tid) {}
        
        allocator_bump(const int numProcesses, debugInfo * const _debug)
                : allocator_interface<T>(numProcesses, _debug)
                , cachelines((sizeof(T)+(BYTES_IN_CACHELINE-1))/BYTES_IN_CACHELINE){
            VERBOSE DEBUG COUTATOMIC("constructor allocator_bump"<<endl);
            mem = new T*[numProcesses*PREFETCH_SIZE_WORDS];
            memBytes = new int[numProcesses*PREFETCH_SIZE_WORDS];
            current = new T*[numProcesses*PREFETCH_SIZE_WORDS];
            toFree = new vector<T*>*[numProcesses];
            for (int tid=0;tid<numProcesses;++tid) {
                mem[tid*PREFETCH_SIZE_WORDS] = 0;
                memBytes[tid*PREFETCH_SIZE_WORDS] = 0;
                current[tid*PREFETCH_SIZE_WORDS] = 0;
                toFree[tid] = new vector<T*>();
            }
        }
        ~allocator_bump() {
            VERBOSE COUTATOMIC("destructor allocator_bump"<<endl);
            // free all allocated blocks of memory
            for (int tid=0;tid<this->NUM_PROCESSES;++tid) {
                int n = toFree[tid]->size();
                for (int i=0;i<n;++i) {
                    free((*toFree[tid])[i]);
                }
                delete toFree[tid];
            }
            delete[] mem;
            delete[] memBytes;
            delete[] current;
            delete[] toFree;
        }
    };

#endif	/* ALLOC_NEW_H */

