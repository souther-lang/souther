package souther.compiler.partition;

import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;

import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumMap;
import java.util.List;
import java.util.Map;

/**
 * Why a reading of a number came to none.
 *
 * <p>What is there and was not kept, and what this compiler never got to. A value the observation
 * did not keep whole is a value that is there, named by the code an observation writes; the rest
 * arrived at no value and have no such code. What a reader does about them differs, so all of them
 * travel, and a quantity stopped in more than one way says each. A quantity that reads several values
 * has one more way to stop after all of them arrived: working out the number they come to, which
 * {@link CouldNotWorkOut} says.
 *
 * <p>Whether a wider run would come to another answer is not what tells them apart. An observation
 * answers it out of the code it carries and the codes do not agree with each other — one a wider
 * run keeps, another it meets again — while the three that reached no value answer alike. So it is
 * a question put to a reason rather than a way of sorting them, and {@link
 * souther.compiler.publish.WeakeningWord}, which sorts them more coarsely still for a document,
 * settles it for none of them.
 *
 * <p><b>{@link NoValue} is a place that was reached.</b> A walk that could not be taken and a row
 * that could not be read are this compiler unable to look, which is not the model putting a value
 * somewhere else; said with the same word, a report tells a reader that nothing was written at a
 * position nothing ever looked at. Each of the three is its own arm so that the sentence written
 * for it is chosen from what happened rather than from an emptiness they share.
 *
 * <p><b>Collected and never chosen between.</b> A rule over several terms is read once per term and
 * a point is tried against several readings of several rows, so the reasons arrive a few at a time
 * and are put together. Ranked instead, every place that folds them writes a precedence, every
 * precedence throws one away, and which one a report says comes out of the order a map or a list
 * happened to be walked in.
 */
public sealed interface ReadingGap {

    /**
     * Whether a run of this compiler that allows more could come to a different answer here.
     *
     * <p>Each arm asks whatever holds the fact rather than answering for it: an observation that
     * stopped carries the code, and the code is what every producer of it agrees about. Which is
     * why the answer does not follow from which arm this is — two observations carry two codes and
     * the codes answer differently — and why nothing coarser than an arm may be asked it.
     */
    RunSensitivity runSensitivity();

    /**
     * The figures of this compiler's that stopped the reading, as each stood where it was compared:
     * empty exactly where {@link #runSensitivity} is {@link RunSensitivity#UNAFFECTED}.
     *
     * <p>Each arm answers, and none from a word: a reader told a wider run may change this is told
     * which figure to widen, and what a reason cannot carry is not said.
     */
    List<Figure> figures();

    /**
     * The observation of a value did not come back whole, and this is what it met.
     *
     * <p>With every figure it was met at, which an observation a limit stopped carries from the
     * walk that stopped it. Several where one code was met at several figures: what a reader is
     * told once is the code ({@code ReadingReasons}), and the figures are what each would take to
     * widen.
     *
     * @param figures in {@link Figure#inOrder}, and present exactly where the code is one a wider
     *                run may change
     */
    record Observation(Incompleteness.Code code, List<Figure> figures) implements ReadingGap {

        public Observation {
            if (code == null || figures == null) {
                throw new IllegalArgumentException("an observation that stopped says what it met");
            }
            figures = Figure.inOrder(figures);
            boolean decided = code.runSensitivity() == RunSensitivity.MAY_CHANGE;
            if (decided == figures.isEmpty()) {
                throw new IllegalArgumentException(decided
                        ? code + " is decided by a figure, and says which"
                        : code + " is decided by no figure, and " + figures + " are");
            }
        }

        @Override
        public RunSensitivity runSensitivity() {
            return code.runSensitivity();
        }

        /** This and {@code other}, which met the same code, as one: met at the figures of both. */
        Observation with(Observation other) {
            if (code != other.code) {
                throw new IllegalArgumentException("two observations are one only where they met"
                        + " one thing: " + code + " and " + other.code);
            }
            List<Figure> both = new ArrayList<>(figures);
            both.addAll(other.figures);
            return new Observation(code, both);
        }
    }

    /** The walk arrived at the position and no value of the row stands there under the reading
     *  being tried, so there was none to observe. */
    record NoValue() implements ReadingGap {

        /** Nothing was compared against a figure: the walk met no value, and it meets none however
         *  much a run is allowed. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }

        @Override
        public List<Figure> figures() {
            return List.of();
        }
    }

    /**
     * The walk into the row could not be taken, so there was no position to read at.
     *
     * <p>What refuses a step is the reading and the value disagreeing about what is at a position,
     * which is a fact about this compiler's walk and says nothing about the row. A row that stands
     * nowhere below a step took it ({@link NoValue}); this one never got that far.
     */
    record CouldNotWalk() implements ReadingGap {

        /** The reading either exposes a name at a position or it does not, and how much a run is
         *  allowed does not enter into it. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }

        @Override
        public List<Figure> figures() {
            return List.of();
        }
    }

    /**
     * A row was asked for and did not come back, so there was nothing to walk.
     *
     * <p>Which of the ways it did not come back — nothing built its values, or the model refused
     * them — is not said here. Both are this compiler unable to put a row in front of the walk, and
     * nothing downstream of the reading acts on the difference; what does tell them apart is
     * {@code RowAsRead.whyNotRead}, and a reader that comes to need it carries it from there rather
     * than from an arm invented here.
     */
    record CouldNotReadRow() implements ReadingGap {

        /** Values that would not build and values the model would not take come back the same way
         *  however much a run is allowed. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }

        @Override
        public List<Figure> figures() {
            return List.of();
        }
    }

    /**
     * Every value the quantity reads came back, and the number they come to is one this compiler
     * could not hold.
     *
     * <p>Not {@link NoValue}: the row wrote something at every position, and saying otherwise tells
     * a reader the row is missing a value it has. And not a reason about the row at all — the
     * numbers are there, and what stopped is this compiler working out how far apart they stand.
     *
     * <p>Which of the two ways the number went unheld travels with it, because a host with more
     * room answers one of them and nothing answers the other, and a reader is told which.
     */
    record CouldNotWorkOut(UnheldNumber why) implements ReadingGap {

        public CouldNotWorkOut {
            if (why == null) {
                throw new IllegalArgumentException("a number not worked out says why it was not");
            }
        }

        /** Unaffected either way: no allowance of this compiler's stopped the working out, and the
         *  room that ran out, where it was room, is the host's. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }

        @Override
        public List<Figure> figures() {
            return List.of();
        }
    }

    /**
     * Whether a run got to the rule through what a reading names — the element an operation that
     * stops at an answer got to, the application of a closure, the arm the way passes — turns on
     * something that could not be read off the row.
     *
     * <p>Not a reason about the value at the point, which was read: the row stands there, and what
     * is not known is whether the run compared anything through that reading of it.
     */
    record ReachNotRead(Why why) implements ReadingGap {

        /** What kept what the way turns on from being read off the row. */
        public enum Why {

            /** A part of it is one nothing read. */
            A_PART_NOT_READ,

            /** A part of it would be read once for more applications than a reading makes. */
            MORE_READINGS_THAN_ARE_MADE,

            /** A part of it is about a container holding more than a walk writes out. */
            MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT,

            /** It is no value the row writes: what a dependency answered, a case nothing here
             *  puts to a row, or an element of a container made of the input's in another order
             *  or of other elements. */
            NO_VALUE_OF_THE_ROW
        }

        public ReachNotRead {
            if (why == null) {
                throw new IllegalArgumentException("what was not read was not read for a reason");
            }
        }

        /** A part declined at how many readings are made, or at how far a container is written
         *  out, is one a run allowing more may read. */
        @Override
        public RunSensitivity runSensitivity() {
            return switch (why) {
                case MORE_READINGS_THAN_ARE_MADE, MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT ->
                        RunSensitivity.MAY_CHANGE;
                case A_PART_NOT_READ, NO_VALUE_OF_THE_ROW -> RunSensitivity.UNAFFECTED;
            };
        }

        /** The figure each of the two a wider run may read past was declined at. Both are fixed
         *  where they are declared, so the figure is the one there is. */
        @Override
        public List<Figure> figures() {
            return switch (why) {
                case MORE_READINGS_THAN_ARE_MADE ->
                        List.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure());
                case MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT -> List.of(
                        WorkFigure.ELEMENTS_A_WALK_WRITES_OUT.at(WrittenOutElements.MOST_WALKED));
                case A_PART_NOT_READ, NO_VALUE_OF_THE_ROW -> List.of();
            };
        }

        /** Why a statement whose reading stopped at {@code unread} could not be read off a row, or
         *  that it is no value of one where nothing in it stopped. */
        public static ReachNotRead of(WhyUnread unread) {
            return new ReachNotRead(switch (unread) {
                case null -> Why.NO_VALUE_OF_THE_ROW;
                case WhyUnread.MoreReadingsThanAreMade _ -> Why.MORE_READINGS_THAN_ARE_MADE;
                case WhyUnread.MoreElementsThanAreWrittenOut _ ->
                        Why.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT;
                default -> Why.A_PART_NOT_READ;
            });
        }
    }

    ReadingGap NO_VALUE = new NoValue();

    ReadingGap REACH_IS_NO_VALUE_OF_THE_ROW =
            new ReachNotRead(ReachNotRead.Why.NO_VALUE_OF_THE_ROW);

    ReadingGap COULD_NOT_WALK = new CouldNotWalk();

    ReadingGap COULD_NOT_READ_ROW = new CouldNotReadRow();

    /** The gap what an observation met is, for a reader holding it: the code, at the figure it
     *  stopped at where one did. */
    static ReadingGap of(Incompleteness.Cause cause) {
        return new Observation(cause.code(), cause.figure().map(List::of).orElseGet(List::of));
    }

    /**
     * {@code met}, with the observations that met one code made one.
     *
     * <p>What a reader is told once is what an observation met, and two readings of one point
     * stopped by one code at two figures are that code met at both. Everything else is handed on as
     * it came, in the order it came.
     */
    static List<ReadingGap> eachObservationOnce(Collection<? extends ReadingGap> met) {
        Map<Incompleteness.Code, Observation> byCode = new EnumMap<>(Incompleteness.Code.class);
        List<ReadingGap> out = new ArrayList<>();
        for (ReadingGap each : met) {
            if (each instanceof Observation it) {
                byCode.merge(it.code(), it, Observation::with);
            } else {
                out.add(each);
            }
        }
        out.addAll(byCode.values());
        return List.copyOf(out);
    }

    /**
     * Why {@code value} cannot be held against another as a whole, or null where it can.
     *
     * <p>Asked of every part of it and not of the value alone. A record one of whose fields a limit
     * stopped is itself a value, and two of them stopped alike are equal as values while what was
     * written in them may differ; a comparison of the two would say they are one where nothing
     * shows it. So a value is compared only where all of it was read ({@link Limits#UNBOUNDED}),
     * and what stopped the reading of any part is what is said.
     */
    static ReadingGap ofAComparisonOf(ObservedValue value) {
        Incompleteness.Cause stopped = Limits.UNBOUNDED.stoppedBy(value);
        return stopped == null ? null : of(stopped);
    }

    /** The gap a number this could not hold is, for a reader that met one. */
    static ReadingGap of(UnheldNumber why) {
        return new CouldNotWorkOut(why);
    }
}
