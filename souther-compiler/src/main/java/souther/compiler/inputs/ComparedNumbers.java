package souther.compiler.inputs;

import souther.compiler.core.Core;

import java.util.IdentityHashMap;
import java.util.Map;

/**
 * The comparisons of one body, each read once.
 *
 * <p>Held rather than read where it is wanted, because more than one reader has to know what a
 * comparison is about — whether a value stands behind each way of settling it, and which decision a
 * run that settled it made — and those are the same question. Asked separately, the two answered
 * from whatever reading each had reached: the same comparison under a binding was a number to one of
 * them and nothing to the other, and what came of that is a decision named for a way nobody held.
 *
 * <p><b>Fixed for the body, and not walked into it.</b> What is here is one reading of the input,
 * the module's names, and what each comparison came to — none of which changes as a reader goes
 * under a binding. What a name reads there does change, so it arrives with the comparison
 * ({@link #of}) from whichever reader is asking, which is already standing at the node.
 *
 * <p>Narrowed with the walk instead, this would copy the reading of the input into every step and
 * leave two scoped values — the reader's own and this one — that answer correctly only while they
 * are at the same node.
 *
 * <p>One comparison is read under one environment. A node occurs once in a body and what is in
 * scope at it is what the walk had when it got there, so a second reading of one node under a
 * different environment is two readers disagreeing about where they are — said as that rather than
 * answered, which is what the environment kept beside each answer is for.
 */
public final class ComparedNumbers {

    /** The reading these comparisons are read against, which is where every position and every
     *  order in an answer below comes from. */
    private final InputReading read;

    /** What each comparison came to and what it was read under, shared by every reader of one
     *  body. */
    private final Map<Core.Binary, Read> said;

    private record Read(InputReads under, ComparedNumber said) { }

    private ComparedNumbers(InputReading read, Map<Core.Binary, Read> said) {
        this.read = read;
        this.said = said;
    }

    /** The comparisons of one body, read against {@code read}. */
    public static ComparedNumbers of(InputReading read) {
        return new ComparedNumbers(read, new IdentityHashMap<>());
    }

    /** The reading they were read against, for a reader that wants it beside them. */
    public InputReading reading() {
        return read;
    }

    /**
     * The reading of {@code comparison} where its names read {@code at}, or null where it names no
     * number of this input.
     *
     * <p>{@code at} comes with the question rather than being held here, because it is what the
     * asking reader is standing at. Two readers meet one comparison at one node, so the second
     * finds the first's answer — and finds it under the environment the first was at, which is
     * what the check below is comparing.
     */
    public ComparedNumber of(Core.Binary comparison, InputReads at) {
        Read had = said.get(comparison);
        if (had != null) {
            if (!had.under().equals(at)) {
                throw new IllegalStateException(
                        "one comparison read under two environments, at " + comparison.pos()
                                + ": what a name reads there is settled by the walk, and two"
                                + " readers of it have arrived with different answers");
            }
            return had.said();
        }
        ComparedNumber made = ComparedNumber.of(comparison, read, at);
        said.put(comparison, new Read(at, made));
        return made;
    }
}
