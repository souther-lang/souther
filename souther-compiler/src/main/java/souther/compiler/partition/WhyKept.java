package souther.compiler.partition;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.reading.PathAccess;

import java.util.Comparator;
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
     * @param written   where the function is
     * @param operation what it is passed to, where it is passed to one the author wrote
     */
    record AFunctionReadAsAWhole(SourcePos written, Optional<String> operation) implements WhyKept {

        public AFunctionReadAsAWhole {
            Objects.requireNonNull(written, "a function is written somewhere");
            Objects.requireNonNull(operation, "what the function is passed to is said or absent");
        }

        /** Where the function is, as a report is entitled to say it. */
        public Citation at() {
            return Citation.of(written);
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

    /**
     * The reasons in one order whatever order they were found in: by kind, then by what tells two
     * of a kind apart.
     *
     * <p>What kept a combination is a set, and the order a report says it in is not part of the
     * answer. Said in the order a walk found them, two readings holding the same reasons would print
     * them two ways, and one held as equal to the other would go on printing the order it was found
     * in first.
     */
    Comparator<WhyKept> IN_A_STEADY_ORDER = Comparator
            .comparingInt(WhyKept::kind)
            .thenComparing((one, other) -> switch (one) {
                case AWayReadInPart(var why) ->
                        why.compareTo(((AWayReadInPart) other).why());
                case AFunctionReadAsAWhole function -> {
                    AFunctionReadAsAWhole that = (AFunctionReadAsAWhole) other;
                    int at = SourcePos.IN_WRITTEN_ORDER.compare(function.written(),
                            that.written());
                    yield at != 0 ? at : function.operation().orElse("")
                            .compareTo(that.operation().orElse(""));
                }
                case ADecisionNothingNames _ -> 0;
                case ARuleNoDecisionReads(var at) ->
                        at.toString().compareTo(((ARuleNoDecisionReads) other).at().toString());
            });

    /** Which kind this is, in the order the kinds are said. */
    private int kind() {
        return switch (this) {
            case AFunctionReadAsAWhole _ -> 0;
            case AWayReadInPart _ -> 1;
            case ADecisionNothingNames _ -> 2;
            case ARuleNoDecisionReads _ -> 3;
        };
    }
}
