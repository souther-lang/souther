package souther.compiler.reading;

import souther.compiler.coverage.ControlClaim;

import java.util.List;

/**
 * What this reading can say about getting to one place in the body.
 *
 * <p>Three answers and never a fourth, and never one of them spelled as the absence of the others.
 * A place with no ways written down could mean the reading proved nothing arrives, or that it could
 * not put the way into words, or that nobody asked — and a caller handed an empty list decided
 * which of those it was by whatever it happened to assume. Each is a value here, and the two that
 * are not {@link Ways} carry why.
 *
 * <p>Not about arms, though an arm is what is asked about first. What a place is — an arm, an
 * operand, a body — is the asker's business; what this says is what holds on the way there.
 *
 * <p>{@link Unreachable} is a fact about the model and {@link Unsupported} is a fact about this
 * compiler. A reader acts on the first (the place is written and no run goes there) and waits on the
 * second (a row through it may well exist, and this reading cannot say what steers one). Written as
 * one, every limit of the reading would read as a proof about the body.
 */
public sealed interface PathAccess {

    /**
     * The ways to it, all of them, and what a run that is here would be seen to have done.
     *
     * <p>Two halves and the second is not the last of the first. What holds on the way to a place
     * and being at the place are different things, and for a fork on a comparison they are said in
     * different vocabularies: the way in is the comparison coming out a way, which a recording
     * answers with {@code saw}, and the place is somewhere a run passes, which it answers with
     * {@code lit}. A {@code match} reads the same both ways round — the case a run matched at is
     * the arm — so a search held to the ways alone passes there and, at a fork on a comparison,
     * certifies a row that was never seen arriving (issue #1009).
     *
     * <p>Never empty. A place this reading reached and found no way to is {@link Unreachable}, and
     * the emptiness would otherwise be a third meaning of the same value.
     *
     * @param arrivesAt what a run that got here is recorded as having done, which is what says a
     *                  row went through this place and not merely where one would be steered
     */
    record Ways(List<WayIn> ways, ControlClaim arrivesAt) implements PathAccess {

        public Ways {
            ways = List.copyOf(ways);
            if (ways.isEmpty()) {
                throw new IllegalArgumentException(
                        "a place reached no way is Unreachable, and says which reading shows it");
            }
            if (arrivesAt == null) {
                throw new IllegalArgumentException(
                        "a place a row is steered to is one a run can be shown to have reached");
            }
        }
    }

    /** No run gets here, and this is what shows it. */
    record Unreachable(Unreachable.Why why) implements PathAccess {

        public Unreachable {
            if (why == null) {
                throw new IllegalArgumentException("a proof about the model names what proves it");
            }
        }

        /** What was read that says no run arrives. */
        public enum Why {

            /** The reading of the condition says it never comes out the way this place is under. */
            THE_CONDITION_NEVER_COMES_OUT_THAT_WAY,

            /** Every way here settles a decision that the way to it settled the other way, which is
             *  read off the decisions themselves and not off anything this could not name. */
            CONTRADICTS_WHAT_ALREADY_HELD
        }
    }

    /** This reading cannot say what the way here is, which is no statement about the body. */
    record Unsupported(Unsupported.Why why) implements PathAccess {

        public Unsupported {
            if (why == null) {
                throw new IllegalArgumentException("what is missing here is what a reader is told");
            }
        }

        /**
         * What this reading is short of.
         *
         * <p>Told apart because they are short of different things. One is what the path language
         * cannot state at all; two are limits this reading holds itself to and would answer
         * differently if the limit moved; two are places a run reaches under something other than
         * this behavior's inputs. A single word over all of them would tell a reader that a place
         * no setting reaches is the same news as one a bound stopped short of.
         */
        public enum Why {

            /** The fork is one no position of the inputs could be named for, so nothing states the
             *  way in however much room a reading is given. */
            NO_WAY_IN_CAN_BE_NAMED,

            /** The ways to the value that leads here could not all be written down, and a list of
             *  some of them is not the ways here. */
            WAYS_NOT_ENUMERABLE,

            /** More ways in than this reading holds at once. What is here is what the limit stopped
             *  short of, and a larger limit reaches it. */
            MORE_WAYS_IN_THAN_ARE_READ,

            /** Inside a function value: the body runs where something calls it, under whatever it is
             *  called with, which is no condition on this behavior's inputs. */
            RUNS_WHERE_SOMETHING_CALLS_IT,

            /** Which arm of an attempted construction is taken is whether the value's own rules held,
             *  and no class of an input names that. */
            THE_CONSTRUCTION_DECIDES_IT
        }
    }
}
