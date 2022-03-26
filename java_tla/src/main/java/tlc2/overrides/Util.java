package tlc2.overrides;

import java.util.ArrayList;
import java.util.Set;

/**
 * Contains functionality for:
 * 1. Permutations
 */
public class Util {

    public static void swap(int[] arr, int i, int j) {
        int t = arr[j];
        arr[j] = arr[i];
        arr[i] = t;
    }

    private static void addPermutationsFromIx(ArrayList<int[]> store, int[] arr, int fromIx, int n) {
        if (fromIx == n) {
            store.add(arr.clone());
        }
        for (int j = fromIx; j < n; j++) {
            swap(arr, fromIx, j);
            addPermutationsFromIx(store, arr, fromIx + 1, n);
            swap(arr, fromIx, j);
        }
    }

    /**
     * Compute permutations on the integer sequence [0, n)
     */
    public static ArrayList<int[]> permutationsOf0toN(int n) {

        ArrayList<int[]> ret = new ArrayList<>();

        int[] arr = new int[n];


        for (int i = 0; i < n; i++){
            arr[i] = i;
        }

        addPermutationsFromIx(ret, arr, 0, n);

        return ret;

    }

    public static <T> ArrayList<ArrayList<T>>  permutations(ArrayList<T> arr){
        ArrayList<int[]> indexPermutations = permutationsOf0toN(arr.size());
        ArrayList<ArrayList<T>> ret = new ArrayList<>();
        for(int i = 0; i < indexPermutations.size(); i++){
            int[] ixPerm = indexPermutations.get(i);
            ArrayList<T> objPerm = new ArrayList<>();
            for(int j = 0; j <arr.size(); j++){
                objPerm.add(arr.get(ixPerm[j]));
            }
            ret.add(objPerm);
        }
        return ret;
    }

    public static <T> ArrayList<ArrayList<T>>  permutations(Set<T> set){
        return permutations(new ArrayList<>(set));
    }
}
