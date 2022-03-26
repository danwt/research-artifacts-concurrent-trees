// from gee.cs.oswego.edu/home/jsr166/jsr166

package jsr166tests.jtreg.util.Collections;

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

/**
 * @test
 * @bug     4323074
 * @summary Basic test for newly public swap algorithm
 * @author  Josh Bloch
 */

import java.util.*;

public class Swap {
    static final int SIZE = 100;

    public static void main(String[] args) throws Exception {
        List l = new ArrayList(Collections.nCopies(100, Boolean.FALSE));
        l.set(0, Boolean.TRUE);
        for (int i=0; i < SIZE-1; i++)
            Collections.swap(l, i, i+1);

        List l2 = new ArrayList(Collections.nCopies(100, Boolean.FALSE));
        l2.set(SIZE-1, Boolean.TRUE);
        if (!l.equals(l2))
            throw new RuntimeException("Wrong result");
    }
}
