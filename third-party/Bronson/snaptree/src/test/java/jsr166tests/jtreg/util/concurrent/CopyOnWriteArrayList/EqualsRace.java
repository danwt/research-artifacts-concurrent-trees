// from gee.cs.oswego.edu/home/jsr166/jsr166

package jsr166tests.jtreg.util.concurrent.CopyOnWriteArrayList;

/*
 * Copyright 2005 Sun Microsystems, Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa Clara,
 * CA 95054 USA or visit www.sun.com if you need additional information or
 * have any questions.
 */

/*
 * @test
 * @bug 6318638 6325166 6330307
 * @summary CopyOnWriteArrayList.equals should be thread-safe
 * @author Martin Buchholz
 */

import java.util.*;
import java.util.concurrent.*;

public class EqualsRace {
    private static void realMain(String[] args) throws Throwable {
        final int iterations = 100000;
        final List<Integer> list = new CopyOnWriteArrayList<Integer>();
        final Integer one = Integer.valueOf(1);
        final List<Integer> oneElementList = Arrays.asList(one);
        final Thread t = new CheckedThread() { public void realRun() {
            for (int i = 0; i < iterations; i++) {
                list.add(one);
                list.remove(one);
            }}};
        t.start();

        for (int i = 0; i < iterations; i++) {
            list.equals(oneElementList);
            list.equals(Collections.EMPTY_LIST);
        }
        t.join();
        check(list.size() == 0);
    }

    //--------------------- Infrastructure ---------------------------
    static volatile int passed = 0, failed = 0;
    static void pass() {passed++;}
    static void fail() {failed++; Thread.dumpStack();}
    static void fail(String msg) {System.out.println(msg); fail();}
    static void unexpected(Throwable t) {failed++; t.printStackTrace();}
    static void check(boolean cond) {if (cond) pass(); else fail();}
    static void equal(Object x, Object y) {
        if (x == null ? y == null : x.equals(y)) pass();
        else fail(x + " not equal to " + y);}
    public static void main(String[] args) throws Throwable {
        try {realMain(args);} catch (Throwable t) {unexpected(t);}
        System.out.printf("%nPassed = %d, failed = %d%n%n", passed, failed);
        if (failed > 0) throw new AssertionError("Some tests failed");}
    private static abstract class CheckedThread extends Thread {
        public abstract void realRun() throws Throwable;
        public void run() {
            try { realRun(); } catch (Throwable t) { unexpected(t); }}}
}
