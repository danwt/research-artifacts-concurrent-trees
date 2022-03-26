package tlc2.overrides;

import org.junit.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

public class UtilTest {

    @Test
    public void permutationsOf0toN() {
        ArrayList<int []> perms = Util.permutationsOf0toN(3);
        assertEquals(6, perms.size());
    }

    @Test
    public void permutationsOfSet() {
        Set<Integer> set = new HashSet<Integer>(){{
            add(0);
            add(1);
            add(2);
            add(3);
            add(4);
            add(5);
        }};
        ArrayList<ArrayList<Integer>> perms = Util.permutations(set);
        assertEquals(720, perms.size()); // 6!
    }

}