package tlc2.overrides;

import tlc2.value.impl.*;
import util.Assert;

import java.util.HashSet;
import java.util.Set;

/**
 * Contains methods for TLA+ to interact with pure Java linearizability functionality.
 */
public class Linearizability {

    private static void validateTuple(Value v) {
        Assert.check(v instanceof TupleValue, "Non tuple type passed to IsLinearizable");
    }

    private static String stripQuotes(String s) {
        return s.replace("\"", "");
    }

    /**
     * Creates a History from a TLC typed Value representing the event sequence.
     */
    private static History toHistory(Value v) {

        /*
         The Pluscal types are like so:
         event_sequence := event_sequence \o <<<<"invoke", self, operation_name, arg>>>>;
         event_sequence := event_sequence \o <<<<"respond", self, succeeded>>>>;

         where self is a process.
         */

        validateTuple(v);

        TupleValue eventList = (TupleValue) v.toTuple();

        Value[] events = eventList.elems;

        History ret = new History();

        for (int i = 0; i < events.length; i++) {

            validateTuple(events[i]);

            TupleValue event = (TupleValue) events[i].toTuple();

            Value[] eventInfo = event.elems;

            String eventTypeName = stripQuotes(eventInfo[0].toString());
            String processName = stripQuotes(eventInfo[1].toString());

            if (eventTypeName.equals("invoke")) {
                String operationName = stripQuotes(eventInfo[2].toString());
                String arg = ((IntValue) eventInfo[3]).toString();
                ret.addInvocationWithNextId(processName, History.OperationType.fromString(operationName),
                        arg);
            } else if (eventTypeName.equals("respond")) {
                // event is 'respond'
                boolean success;
                try {
                    success = ((BoolValue) eventInfo[2]).getVal();
                } catch (Exception e) {
                    // Boolean is 1 or 0 instead of 'TRUE' or 'FALSE'
                    int val = ((IntValue) eventInfo[2]).val;
                    success = val != 0;
                }
                ret.addResponse(processName, success);
            }

        }
        return ret;
    }

    private static Set<Integer> toIntegerSet(Value v) {
        Set<Integer> ret = new HashSet<>();
        SetEnumValue s = (SetEnumValue) v;
        Value[] elements = s.elems.toArray();
        for (Value e : elements) {
            IntValue iv = (IntValue) e;
            ret.add(iv.val);
        }
        return ret;
    }

    /**
     * @param history    the event sequence
     * @param startState the set of keys already present in the Set ADT
     */
    @TLAPlusOperator(identifier = "IsLinearizable", module = "Linearizability")
    public static Value IsLinearizable(Value history, Value startState) {
        History h = toHistory(history);
        Set<Integer> ss = toIntegerSet(startState);
        return new BoolValue(h.isLinearizable( ss));
    }

}