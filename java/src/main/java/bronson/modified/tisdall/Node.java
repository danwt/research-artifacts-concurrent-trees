package bronson.modified.tisdall;

import lombok.AllArgsConstructor;

@AllArgsConstructor
public class Node {

    static final int SpinCount = Integer.parseInt(System.getProperty("snaptree.spin", "100"));

    static final int YieldCount = Integer.parseInt(System.getProperty("snaptree.yield", "0"));

    static boolean isShrinking(long ver) {
        return (ver & 1) != 0;
    }

    final Integer key;
    volatile int height;
    volatile Object val;
    volatile bronson.modified.tisdall.Node parent;
    volatile long ver;
    volatile bronson.modified.tisdall.Node left;
    volatile bronson.modified.tisdall.Node rite;

    public bronson.modified.tisdall.Node Child(char dir) {
        return dir == 'L' ? left : rite;
    }

    public void setChild(char dir, bronson.modified.tisdall.Node node) {
        if (dir == 'L') {
            left = node;
        } else {
            rite = node;
        }
    }

    public void WaitUntilShrinkCompleted(final long ver) {
        if (!isShrinking(ver)) {
            return;
        }

        for (int tries = 0; tries < SpinCount; ++tries) {
            if (this.ver != ver) {
                return;
            }
        }

        for (int tries = 0; tries < YieldCount; ++tries) {
            Thread.yield();
            if (this.ver != ver) {
                return;
            }
        }

        synchronized (this) {

        }
    }
}
