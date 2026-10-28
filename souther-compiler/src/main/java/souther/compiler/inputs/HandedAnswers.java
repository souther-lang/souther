package souther.compiler.inputs;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;

/**
 * What a reading asked of the values an application handed to the names on the way to it, and the
 * answers it was given: a name to the value it was handed, or to nothing where it was handed none.
 *
 * <p>A reading that asked these and nothing else of what was handed comes to the same on any
 * reading whose answers they are, whatever else it was handed ({@link InputReads#handsAsAsked}).
 */
public final class HandedAnswers {

    /** What a reading that is not to be told from another by what it asked asked: it compared
     *  whole environments, or was run inside another watch. Holds of no reading. */
    public static final HandedAnswers UNTOLD = new HandedAnswers(Map.of(), false);

    private final Map<BindingId, Core> answers;
    private final boolean toldApart;

    HandedAnswers(Map<BindingId, Core> answers) {
        this(answers, true);
    }

    private HandedAnswers(Map<BindingId, Core> answers, boolean toldApart) {
        this.answers = new LinkedHashMap<>(answers);
        this.toldApart = toldApart;
    }

    /** Whether a reading that asked these is told from another by them. */
    public boolean toldApart() {
        return toldApart;
    }

    boolean holdsOf(BindingEnvironment names) {
        if (!toldApart) {
            return false;
        }
        for (Map.Entry<BindingId, Core> each : answers.entrySet()) {
            if (!Objects.equals(each.getValue(), names.handedUnwatched(each.getKey()))) {
                return false;
            }
        }
        return true;
    }
}
