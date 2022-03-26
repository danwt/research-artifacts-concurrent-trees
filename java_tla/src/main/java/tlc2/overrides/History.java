package tlc2.overrides;

import java.util.*;

/*
 * Build a history and check that it is linearizable

 * By default, check against a Set ADT
 * Insert(k) - returns bool(k was absent and insert succeeded)
 * Erase(k) - returns bool(k was present and erase succeeded)
 * Get(k) - returns bool(k was present)

 * There is the matter of matching the true definition of linearizability. That is: for
 * histories where not every invocation has a response - can we extend the history with responses
 * such that the history is sequentially consistent?
 * We just assume that the history is complete; meaning that every invocation has a
 * response.
 *
 * Algorithm:
 * Save the operation list with invocations and responses combined.
 * Test all permutations (sequential histories) for 2 things:
 * 1. It's consistent against the Set ADT
 * 2. Operations are consistent with happens-before (after) relationships defined
 * by the order of invocations and responses.
 */
class History {

    static class SetADT {

        private Set<String> impl = new HashSet<String>();

        boolean insert(String k) {
            boolean ret = !impl.contains(k);
            impl.add(k);
            return ret;
        }

        boolean erase(String k) {
            boolean ret = impl.contains(k);
            impl.remove(k);
            return ret;
        }

        boolean get(String k) {
            boolean ret = impl.contains(k);
            return ret;
        }

    }

    enum OperationType {
        INSERT,
        ERASE,
        GET;

        static OperationType fromString(String s) {
            if (s.equals("insert")) {
                return OperationType.INSERT;
            }
            if (s.equals("erase")) {
                return OperationType.ERASE;
            }
            if (s.equals("get")) {
                return OperationType.GET;
            }
            throw new IllegalArgumentException("operationTypeString not " +
                    "recognized");
        }
    }

    static class Operation {
        Integer id;
        String processName;
        OperationType operationType;
        String arg;
        boolean returnValue;
    }

    Integer nextId = 0;
    Map<Integer, Operation> operations = new HashMap<>();
    Set<Integer> openSet = new HashSet<>();
    Set<Integer> closedSet = new HashSet<>();

    // Map an operation to the set of operations that respond before the invocation
    Map<Integer, Set<Integer>> happensBefore = new HashMap<>();

    // Map an operation to the set of operations that are invoked after the response
    Map<Integer, Set<Integer>> happensAfter = new HashMap<>();

    void addInvocation(String processName, OperationType operationType,
                       String arg, Integer id) {

        Operation op = new Operation();
        op.id = id;
        op.processName = processName;
        op.operationType = operationType;
        op.arg = arg;

        operations.put(op.id, op);

        openSet.add(op.id);

        happensBefore.put(op.id, new HashSet<Integer>(closedSet));
        happensAfter.put(op.id, new HashSet<Integer>());

        closedSet.forEach(it -> {
            happensAfter.get(it).add(op.id);
        });
    }

    void addInvocationWithNextId(String processName, OperationType operationType,
                                 String arg) {
        Integer id = nextId++;
        addInvocation(processName, operationType, arg, id);
    }

    private Operation getOpenOperationForProcess(String processName) {
        try {
            return operations.get(openSet.stream().filter(it -> operations.get(it).processName.equals(processName)).findFirst().get());
        } catch (NoSuchElementException e) {
            throw new NoSuchElementException("addResponse called but the " +
                    "process did not have an open operation");
        }
    }

    void addResponse(String processName, boolean returnValue) {
        Operation op = getOpenOperationForProcess(processName);
        op.returnValue = returnValue;
        openSet.remove(op.id);
        closedSet.add(op.id);
    }

    static boolean isValidSequentialOrdering(History underTest,
                                             ArrayList<Integer> sequentialOrdering,
                                             Set<Integer> startState
    ) {

        History compare = new History();

        SetADT set = new SetADT();
        for (Integer k : startState) {
            set.insert(k.toString());
        }

        // Check that the sequential ordering is actually a valid execution
        // according to the data structure
        for (Integer opId : sequentialOrdering) {

            Operation it = underTest.operations.get(opId);

            compare.addInvocation(it.processName, it.operationType, it.arg, it.id);
            compare.addResponse(it.processName, it.returnValue);

            boolean sequentialReturnValue;

            switch (it.operationType) {
                case INSERT:
                    sequentialReturnValue = set.insert(it.arg);
                    break;
                case ERASE:
                    sequentialReturnValue = set.erase(it.arg);
                    break;
                case GET:
                    sequentialReturnValue = set.get(it.arg);
                    break;
                default:
                    throw new IllegalArgumentException("OperationType enum" +
                            " not fully enumerated in switch");
            }

            if (sequentialReturnValue != it.returnValue) {
                return false;
            }
        }

        // Check that happens before/after relationships are respected
        for (Integer opId : sequentialOrdering) {
            Set<Integer> underTestHappensBefore = underTest.happensBefore.get(opId);
            Set<Integer> underTestHappensAfter = underTest.happensAfter.get(opId);
            Set<Integer> compareHappensBefore = compare.happensBefore.get(opId);
            Set<Integer> compareHappensAfter = compare.happensAfter.get(opId);
            if (!Collections.disjoint(underTestHappensAfter, compareHappensBefore)) {
                return false;
            }
            if (!Collections.disjoint(underTestHappensBefore, compareHappensAfter)) {
                return false;
            }
        }

        return true;
    }

    /**
     * @param startState the set of keys already contained in the set ADT before the history begins.
     */
     boolean isLinearizable( Set<Integer> startState) {

        assert this.openSet.isEmpty() : "isLinearizable called on history but" +
                " not all invoked operations have responses";

        assert this.nextId == this.closedSet.size() : "the set of operations " +
                "with responses has fewer elements than the number of " +
                "operation ids given";

        return Util.permutations(this.closedSet).stream().anyMatch(it -> isValidSequentialOrdering(this
                , it, startState));
    }
}
