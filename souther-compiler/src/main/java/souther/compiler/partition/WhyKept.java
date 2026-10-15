package souther.compiler.partition;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.reading.PathAccess;
import souther.compiler.semantics.HowAClosureIsApplied;

import java.util.Comparator;
import java.util.List;
import java.util.Objects;

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
     * some use of the function is other than an operation of the language applying it once to each
     * element of a position of the input ({@link WithinOneApplication}).
     *
     * @param written    where the function is
     * @param shortfalls each use that falls short, read off the uses the judgment was made from
     *                   ({@link souther.compiler.check.ClosureUses}) — so a function two operations
     *                   apply names the one that does not apply it so, and not the other
     */
    record AFunctionReadAsAWhole(SourcePos written, List<Shortfall> shortfalls)
            implements WhyKept {

        public AFunctionReadAsAWhole {
            Objects.requireNonNull(written, "a function is written somewhere");
            shortfalls = List.copyOf(shortfalls);
            if (shortfalls.isEmpty()) {
                throw new IllegalArgumentException("a function read as a whole is short of"
                        + " something");
            }
        }

        /** Where the function is, as a report is entitled to say it. */
        public Citation at() {
            return Citation.of(written);
        }
    }

    /** One use of a function that is not an operation applying it once to each element of a
     *  position of the input. */
    sealed interface Shortfall {

        /** Something other than an operation of the language applies the function, or may: it is
         *  applied directly, handed to a function of the author's, or kept in a value. */
        record NotOnlyByOperations() implements Shortfall {}

        /**
         * {@code operation} applies the function to some of the elements and not each of them.
         *
         * @param operation what the author called, as they wrote it
         * @param applied   how far it goes, which is never to every element
         */
        record ToSomeOfTheElements(String operation, HowAClosureIsApplied applied)
                implements Shortfall {

            public ToSomeOfTheElements {
                Objects.requireNonNull(operation, "some operation applies it");
                if (applied == HowAClosureIsApplied.TO_EVERY_ELEMENT) {
                    throw new IllegalArgumentException("`" + operation + "` applies it to every"
                            + " element, which falls short of nothing");
                }
            }
        }

        /**
         * {@code operation} applies the function over a container that is no position of the
         * input: what another operation answered, or values written out.
         *
         * @param operation what the author called, as they wrote it
         */
        record OverNoPosition(String operation) implements Shortfall {

            public OverNoPosition {
                Objects.requireNonNull(operation, "some operation applies it");
            }
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
                    yield at != 0 ? at : function.shortfalls().toString()
                            .compareTo(that.shortfalls().toString());
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
