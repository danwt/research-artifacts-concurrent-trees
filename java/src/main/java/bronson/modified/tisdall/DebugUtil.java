package bronson.modified.tisdall;

import util.JsonGraph;

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;
import java.util.function.Function;

public class DebugUtil {

    static class Recursive<F> {
        F fun;
        boolean good = true;
    }

    public static List<JsonGraph.Edge> edgeList(Node rootHolder) {

        List<JsonGraph.Edge> edges = new ArrayList<JsonGraph.Edge>();

        Recursive<Consumer<Node>> f =
                new Recursive<>();

        Function<Node, String> label = (Node n) ->
                MessageFormat.format("\"key:{0} val:{1}\"", n.key, n.val == null ? "-1" : n.val);

        f.fun = node -> {
            if (node == null) {
                return;
            }
            String lbl = label.apply(node);
            if (node.left != null) {
//                edges.add(new JsonGraph.Edge(lbl, label.apply(node.left), true)); TODO: this should be updated to match new JsonGraph api
            }
            if (node.rite != null) {
//                edges.add(new JsonGraph.Edge(lbl, label.apply(node.rite), false)); TODO: this should be updated to match new JsonGraph api
            }
            f.fun.accept(node.left);
            f.fun.accept(node.rite);
        };

        f.fun.accept(rootHolder);
        return edges;
    }

    public static boolean heightsFieldsAreCorrect(Node root) {

        Recursive<Function<Node, Integer>> f =
                new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return 0;
            }
            int lh = f.fun.apply(node.left);
            int rh = f.fun.apply(node.rite);
            int h = SnapTreeMapIterativeBrown.MaxPlusOne(lh, rh);
            if (node.height != h) {
                f.good = false;
            }
            return h;
        };

        f.fun.apply(root);

        return f.good;
    }

    public static boolean trueBalance(Node root) {

        Recursive<Function<Node, Integer>> f =
                new Recursive<>();

        f.fun = node -> {
            if (node == null) {
                return 0;
            }
            int lh = f.fun.apply(node.left);
            int rh = f.fun.apply(node.rite);
            if (SnapTreeMapIterativeBrown.BalanceFactorIsImBalanced(lh - rh)) {
                f.good = false;
            }
            return SnapTreeMapIterativeBrown.MaxPlusOne(lh, rh);
        };

        f.fun.apply(root);

        return f.good;
    }

    public static boolean invariantsHold(Node rootHolder) {
        boolean good = true;
        good = good && trueBalance(rootHolder.rite);
        good = good && heightsFieldsAreCorrect(rootHolder.rite);
        return good;
    }

}