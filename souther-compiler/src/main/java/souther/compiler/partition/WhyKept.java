package souther.compiler.partition;

import souther.compiler.diag.Citation;
import souther.compiler.reading.PathAccess;

import java.util.Objects;
import java.util.Optional;

/**
 * Why a combination of two classes is owed where no way of the body that was read whole reads the
 * two together.
 *
 * <p>What the reading could not say stays a combination ({@link ReadTogether}), and this is what it
 * could not say. A reader told only that a combination is owed is sent to write a row; told this
 * as well, the reader can tell a combination the body brings together from one the reading did not
 * get far enough to rule out, and knows what in the body to look at.
 */
public sealed interface WhyKept {

    /**
     * A way of the body holds a step this reading has no words for, or a bound it stopped reading
     * at, so what the way read together may be any of the positions.
     */
    record AWayReadInPart(PathAccess.Unsupported.Why why) implements WhyKept {

        public AWayReadInPart {
            Objects.requireNonNull(why, "a way is read in part for a reason");
        }
    }

    /**
     * The ways inside a function value were read as a whole, and not one application at a time:
     * something applies the function other than once to each element of a position of the input
     * ({@link WithinOneApplication}).
     *
     * @param at        where the function is written
     * @param operation what it is passed to, where it is passed to one where it is written
     */
    record AFunctionReadAsAWhole(Citation at, Optional<String> operation) implements WhyKept {

        public AFunctionReadAsAWhole {
            Objects.requireNonNull(at, "a function is written somewhere");
            Objects.requireNonNull(operation, "what the function is passed to is said or absent");
        }
    }

    /** A way of the body holds a decision whose subject the reading could not name, which may be
     *  about any of the positions. */
    record ADecisionNothingNames() implements WhyKept {}

    /** The body wrote a rule dividing the position {@code at} that no decision the ways read is a
     *  reading of, so what the position is read beside is not known. */
    record ARuleNoDecisionReads(AxisId at) implements WhyKept {

        public ARuleNoDecisionReads {
            Objects.requireNonNull(at, "a rule divides some position");
        }
    }
}
