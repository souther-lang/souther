package souther.compiler.check;

import souther.compiler.core.Contract;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * A behavior's {@code ensures} as this compile read it: the declaration, and the reading of it that
 * runs.
 *
 * <p>Two products of one reading, and they are handed over together because that is what makes them
 * one reading. A caller asking for the declaration and a caller asking for what runs would
 * otherwise be asking two questions, and the second of them would be answered by whoever needed it
 * — which is where the second elaboration was (issue #1080).
 *
 * <p>Nothing joins a rule of one to a rule of the other, and nothing has to: what wants the places,
 * the arms and the clause a rule was written under reads {@link #read()}, and what has to decide
 * whether an answer keeps the declaration reads {@link #checked()}. They are held to being the same
 * declaration by there being one walk that makes both, and to nothing else — a rule numbered in one
 * and looked up in the other would be the alignment this deliberately does not offer.
 */
public record CheckedEnsures(BehaviorContract read, Contract checked) {

    /**
     * The executable half of what a module's behaviors declare, by the name each is declared under.
     *
     * <p>What an emitter, a row and a checked program are given. Said here so that the reading a
     * check is emitted from is picked out in one place: three callers each reaching into the pair
     * would be three readers deciding for themselves which half a check runs.
     */
    public static Map<String, Contract> executable(Map<String, CheckedEnsures> declared) {
        Map<String, Contract> out = new LinkedHashMap<>();
        declared.forEach((behavior, ensures) -> out.put(behavior, ensures.checked()));
        return out;
    }

    public CheckedEnsures {
        if (read == null || checked == null) {
            throw new IllegalArgumentException("a declaration is read and elaborated together");
        }
        if (read.rules().size() != checked.rules().size()) {
            // One walk made both, so this is that walk having gone wrong rather than a caller
            // having passed the wrong pair. Said here because a contract short of a rule states
            // less than the author wrote, and nothing downstream could tell.
            throw new IllegalStateException("`" + read.behavior().name() + "` read "
                    + read.rules().size() + " rules and elaborated " + checked.rules().size());
        }
    }
}
