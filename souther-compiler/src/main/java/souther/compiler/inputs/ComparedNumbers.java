package souther.compiler.inputs;

import souther.compiler.check.Symbols;
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
 * <p><b>Scoped like the reading it is made of.</b> What a name reads is not a fact about the node
 * that reads it, so this narrows at each binder the way the reading of the input does, and a reader
 * that walks into a body walks this in with it.
 *
 * <p>One comparison is read under one environment. A node occurs once in a body and what is in
 * scope at it is what the walk had when it got there, so a second reading of one node under a
 * different environment is two readers disagreeing about where they are — said as that rather than
 * answered.
 */
public final class ComparedNumbers {

    // Beside the module's names and for the same reason: one body is read against one reading of
    // the input, while what a name stands for is whatever the walk has got to.
    private final InputDomain inputs;
    private final InputReads reads;
    private final Symbols symbols;

    /** What each comparison came to and what it was read under, shared by every scope of one body. */
    private final Map<Core.Binary, Read> said;

    private record Read(InputReads under, ComparedNumber said) { }

    private ComparedNumbers(InputDomain inputs, InputReads reads, Symbols symbols,
                            Map<Core.Binary, Read> said) {
        this.inputs = inputs;
        this.reads = reads;
        this.symbols = symbols;
        this.said = said;
    }

    /** The comparisons of a body whose names read {@code reads}, against {@code inputs}. */
    public static ComparedNumbers of(InputDomain inputs, InputReads reads, Symbols symbols) {
        return new ComparedNumbers(inputs, reads, symbols, new IdentityHashMap<>());
    }

    /** What a name reads inside a body that binds {@code binder} to {@code value}. */
    public ComparedNumbers under(Core.Binder binder, Core value) {
        InputReads inside = reads.and(binder, value);
        return inside.equals(reads) ? this : new ComparedNumbers(inputs, inside, symbols, said);
    }

    /** What a name reads inside {@code arm} of {@code match}, where the arm's name stands for the
     *  value matched read as the case the arm selects. The other of the two scope transitions the
     *  reading of the input has, and this has both for the same reason it is scoped at all. */
    public ComparedNumbers insideArm(Core.Match match, Core.Case arm) {
        InputReads inside = reads.insideArm(match, arm, symbols);
        return inside.equals(reads) ? this : new ComparedNumbers(inputs, inside, symbols, said);
    }

    /** The reading of {@code comparison}, or null where it names no number of this input. */
    public ComparedNumber of(Core.Binary comparison) {
        Read had = said.get(comparison);
        if (had != null) {
            if (!had.under().equals(reads)) {
                throw new IllegalStateException(
                        "one comparison read under two environments, at " + comparison.pos()
                                + ": what a name reads there is settled by the walk, and two"
                                + " readers of it have arrived with different answers");
            }
            return had.said();
        }
        ComparedNumber read = ComparedNumber.of(comparison, inputs, reads, symbols);
        said.put(comparison, new Read(reads, read));
        return read;
    }
}
