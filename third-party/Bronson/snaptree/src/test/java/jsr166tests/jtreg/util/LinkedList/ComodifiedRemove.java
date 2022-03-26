// from gee.cs.oswego.edu/home/jsr166/jsr166

package jsr166tests.jtreg.util.LinkedList;

/*
 * Copyright 2000 Sun Microsystems, Inc.  All Rights Reserved.
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
 * @bug 4308549
 * @summary Due to a bug in LinkedList's ListIterator's remove(),
 *     the ListIterator would not check for comodification before remove.
 * @author Konstantin Kladko
 */

import java.util.*;
import java.util.ListIterator;
import java.util.ConcurrentModificationException;

public class ComodifiedRemove {
    public static
    void main(String[] args) {
        List list = new LinkedList();
        Object o1 = new Integer(1);
        list.add(o1);
        ListIterator e = list.listIterator();
        e.next();
        Object o2 = new Integer (2);
        list.add(o2);

        try{
            e.remove();
        } catch (ConcurrentModificationException cme) {
            return;
        }

        throw new RuntimeException(
            "LinkedList ListIterator.remove() comodification check failed.");
    }
}
