package souther.compiler.inputs;

import souther.compiler.check.BoundaryClaim;
import souther.compiler.check.CoverageObligation;

/**
 * What one coverage question is about, in the vocabulary of an input rather than of a declaration's
 * own fields.
 *
 * <p><b>The same questions {@code check.Owed} carries, and not the same identities.</b> A reading of
 * a declaration knows its positions by a key relative to the value the clauses are written on —
 * {@code x}, {@code a.b}, the empty string for the value itself — and knows a number of one by the
 * operation beside that key. What an input is walked by is a {@link TermPath} from a parameter, and
 * what a boundary is drawn on is a {@link NumericTerm}. Neither can be read off the other without
 * the root the walk started at and the type standing at the position, which only the boundary
 * between the two has.
 *
 * <p>So the crossing is made once, where those are, and everything downstream compares these. Left
 * in the declaration's vocabulary and compared against an axis, a field key and a term path are two
 * spellings of one place that agree at a top-level parameter and nowhere else — and comparing them
 * as strings is the reconstruction this whole side exists to stop.
 *
 * <p>The same crossing {@link UnreadRule} makes with {@link FilingCoordinate}, and for the same
 * reason: a finding about a rule and a question about a rule are both filed at a number, and the
 * number is named where the input's own vocabulary is.
 */
public sealed interface InputQuestion {

    /**
     * Which values may stand at a position of the input.
     *
     * <p>The position and never a number of it: what a rule about the length of a string admits is
     * a set of strings.
     */
    record AboutAPosition(TermPath path) implements InputQuestion {

        public AboutAPosition {
            if (path == null) {
                throw new IllegalArgumentException("a position sits somewhere in the input");
            }
        }

        @Override
        public String toString() {
            return path.toString();
        }
    }

    /**
     * Where a line falls on one number of one position.
     *
     * <p>The claim, which names the operation for a number taken of a position and the position
     * itself for its own values. Two operations over one path are two of these and are told apart
     * here rather than by whatever a reader finds standing beside them.
     *
     * <p><b>Not the term.</b> A {@link NumericTerm} exists where a reading worked out what the
     * number is measured by and how it is read off a row, so a question holding one could be asked
     * only about a rule this compiler had already got through — and a rule whose number nothing
     * could be made of asked nothing at all. The claim is what the author wrote: a place and the
     * operation their call resolved to. Whoever answers builds the term from it, and where none can
     * be built the question stands unanswered rather than unasked.
     */
    record AboutANumber(BoundaryClaim<TermPath> claim) implements InputQuestion {

        public AboutANumber {
            if (claim == null) {
                throw new IllegalArgumentException("a line falls on some number");
            }
        }

        @Override
        public String toString() {
            return claim.toString();
        }
    }

    /** Where in the input the question sits, which both arms can always say. */
    default TermPath path() {
        return switch (this) {
            case AboutAPosition it -> it.path();
            case AboutANumber it -> it.claim().position();
        };
    }

    /** What it asks, which is the arm. */
    default CoverageObligation obligation() {
        return switch (this) {
            case AboutAPosition _ -> CoverageObligation.ADMITTED_VALUES;
            case AboutANumber _ -> CoverageObligation.BOUNDARY;
        };
    }
}
