package souther.compiler.query;

import souther.compiler.inputs.EmptyInput;
import souther.compiler.observe.MeasureReason;

/**
 * There is nothing for a measure of a behavior's input to be about, because the rules reaching that
 * input leave it no value.
 *
 * <p>Not a gap. A gap is a row nobody has written and somebody could; here no row exists to write,
 * so nothing is missing and no author is being asked for anything. Counted as one, a model whose
 * declarations contradict would be held open for tests that cannot be written.
 *
 * <p>Not a reading that fell short either. This is what the reading concluded, from every parameter's
 * rules held together — which is where a contradiction between two declarations is visible and the
 * only place it is.
 *
 * <p><b>One proof about the input, and each measure of it publishes its own inapplicability from
 * that proof.</b> The proof is made once, where every parameter's rules are held together, because
 * that is the only place a contradiction between two declarations is visible; a partition and a
 * border then each say they have no subject and neither works out why. Derived per measure, two of
 * them would be free to disagree about one model; said per rule or per position, it would be said
 * once for each and every time about a rule that is not at fault — two clauses each admitting values
 * are empty together, and neither of them is the one that failed.
 *
 * <p>What a document carries is the second of those, once per measure. Which measures have no
 * subject is what a reader of a measure's {@code reason} is asking, and a behavior-level field
 * saying it a third time would be the same fact in a place nothing else about a measure is written.
 *
 * @param proof what the rules were found to leave nothing by. Carried rather than reduced to the
 *              word, so that a reader wanting to say which contradiction it was has it and the
 *              published word stays one
 */
public record NoFeasibleInput(EmptyInput proof) implements NotApplicableReason {

    /** The word a document writes for it. */
    public static final String WORD = "no_feasible_input";

    /** One word for every proof of it. Which contradiction the rules held is in {@link #proof} and
     *  is not what a document promises its reader they can tell apart. */
    @Override
    public String name() {
        return WORD;
    }

    @Override
    public MeasureReason.About about() {
        return MeasureReason.About.THE_BEHAVIOR;
    }

    public NoFeasibleInput {
        if (proof == null) {
            throw new IllegalArgumentException(
                    "an input the rules leave empty is one they were proved to leave empty");
        }
    }
}
