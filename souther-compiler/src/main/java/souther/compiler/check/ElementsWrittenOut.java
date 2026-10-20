package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import net.unit8.notation199x.ScalarValues;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.OptionalLong;

/**
 * Every element a container holds, written out, in the order a walk of it meets them and each with
 * what it was kept by — where the container is a list written in the source, the code points of a
 * text written in the source, a list an operation put together of a piece of each element of one
 * ({@link ElementBindings#piecesOfEachElement}), or a list a choice answers ({@link Choice}), each
 * of its arms one of these.
 *
 * <p>One walk for every reader that writes a container out, whatever it reads names in. The reading
 * of an input and the discharge of a rule read names in two environments, and each hands this the
 * two things it asks of one ({@link Reading}); which elements a container holds, in which order and
 * kept by what, is decided here and nowhere else. Two walks would be two answers the first time one
 * of them learned an operation the other did not — a rule measured as {@code c - 48} and checked as
 * {@code c} less some number.
 *
 * <p>What each piece is, is what the operation is proved to make of an element, and nothing read
 * off its name. A map's piece is the step's answer on the element, read where the step is handed
 * it; a filter's is the element itself, kept where the step's answer on it holds; a flatMap's is
 * every element of the step's answer on it, written out by this same walk. A choice's are every
 * element of each arm, kept where the arm is taken. What an occurrence was kept by is carried down
 * every level, each truth read where it was decided.
 *
 * <p>An occurrence a filter dropped is written out as well, kept where its truth holds. Whether it
 * holds is a question about the values, and the answer is a reader's. What this answers itself is
 * the narrower question of what is there on every run ({@link #sizeOf}, {@link #picked}), where a
 * truth that comes out the same every time is that answer on every run.
 */
public final class ElementsWrittenOut {

    /**
     * How many occurrences a walk writes out, at every level it passes, before it stops.
     *
     * <p>A bound on the work and not on what a reader takes: an occurrence a filter drops and one at
     * a level a flatMap goes through are written out as much as one in the answer. Past it the
     * container is one this could write out and does not. No reader of a condition takes more
     * applications of a closure than the readings it reads one condition in, so this is held above
     * that figure and leaves room for the levels on the way to it.
     */
    public static final int MOST_WALKED = 1024;

    private ElementsWrittenOut() {
    }

    /**
     * What a walk asks of the environment {@code E} a reader reads names in.
     *
     * @param <E> the environment
     */
    public interface Reading<E> {

        /** The library {@code Kernel}s are looked up against. */
        Symbols symbols();

        /** {@code e} where it stands in {@code at}, followed through the names it was given. */
        Stood<E> standing(Core e, E at);

        /** {@code at} with {@code element} handed {@code value}, as an application of a step to an
         *  element hands its parameter one. */
        E handing(E at, BindingId element, Stood<E> value);

        /** {@code at} with what choosing the arm {@code decidedBy} decides entered, as the arm's
         *  answer is read. */
        E choosing(E at, Choice.Decides decidedBy);

        /** What {@code value} comes to at compile time where it stands ({@link FoldedValue}), or
         *  empty where it is no constant. */
        Optional<Object> folded(Stood<E> value);
    }

    /** An expression and the environment its names are read in, which travel together. */
    public record Stood<E>(Core value, E at) {

        public Stood {
            Objects.requireNonNull(value, "a value stands somewhere");
        }
    }

    /**
     * One element a container holds where every one of {@code keptWhere} holds.
     *
     * @param keptWhere the truths it was kept by, each read where it was decided, those decided
     *                  first first — none where nothing keeps it out
     * @param answered  which application of the step that made {@code value} this is, counting from
     *                  none in the order the step is handed the elements of its container, where
     *                  that is also the run's own count of the step's applications: every element
     *                  the step was handed up to this one was handed it on every run. Empty where
     *                  {@code value} is no step's answer, and where an element before it may have
     *                  been dropped — past a drop a run applies the step to fewer, and which
     *                  application this is is not something the container says
     */
    public record Occurrence<E>(Stood<E> value, List<Kept<E>> keptWhere, OptionalInt answered) {

        public Occurrence {
            Objects.requireNonNull(value, "an occurrence is of some value");
            keptWhere = List.copyOf(keptWhere);
            Objects.requireNonNull(answered,
                    "an occurrence is answered by some application or none");
        }

        static <E> Occurrence<E> always(Stood<E> value) {
            return new Occurrence<>(value, List.of(), OptionalInt.empty());
        }

        Occurrence<E> keptAlsoWhere(List<Kept<E>> more) {
            List<Kept<E>> all = new ArrayList<>(more);
            all.addAll(keptWhere);
            return new Occurrence<>(value, all, answered);
        }
    }

    /** What an occurrence was kept by. */
    public sealed interface Kept<E> {

        /**
         * A truth, and which way it came out: a filter's step on the element.
         *
         * <p>Of one application of the step, and the occurrences made of what an application kept
         * are kept by that one application and say so. A flatMap after a filter writes the same
         * kept element out twice; the step was applied to it once, and two occurrences are not two
         * applications.
         *
         * @param application which application of the step this is, counting from none in the
         *                    order the step is handed the elements of the container it filters.
         *                    The step is handed each of them, so this is also the run's own count
         *                    of the step's applications where nothing before it dropped an element
         *                    on the way; past a drop a run applies the step to fewer, and the
         *                    count is the reader's to say it cannot take from this
         */
        record ATruth<E>(Stood<E> truth, boolean holds, int application) implements Kept<E> {

            public ATruth {
                Objects.requireNonNull(truth, "an occurrence is kept by some truth");
                if (application < 0) {
                    throw new IllegalArgumentException(
                            "applications are counted from none: " + application);
                }
            }
        }

        /**
         * The arm {@code part} of {@code fork} being the one a run takes, as {@link Choice}
         * numbers its arms.
         *
         * <p>The fork and not what decides the arm, because an arm is taken where its own way of
         * being decided holds and no arm before it was taken: which one is taken is a fact of the
         * whole fork.
         */
        record AnArm<E>(Stood<E> fork, int part) implements Kept<E> {

            public AnArm {
                Objects.requireNonNull(fork, "an arm is an arm of some fork");
            }
        }
    }

    /** What a walk of a container came to. */
    public sealed interface Walked<E> {

        /** The occurrences, in order — every one of them, or as many as were asked for. */
        record Each<E>(List<Occurrence<E>> each) implements Walked<E> {

            public Each {
                each = List.copyOf(each);
            }
        }

        /** More than {@link #MOST_WALKED} on the way. */
        record PastTheFigure<E>() implements Walked<E> {}

        /** Not a container this walk writes out. */
        record NotWrittenOut<E>() implements Walked<E> {}
    }

    /** Every element {@code container} holds. */
    public static <E> Walked<E> of(Stood<E> container, Reading<E> reading) {
        return of(container, reading, Integer.MAX_VALUE, new int[] {0});
    }

    /**
     * How many elements {@code container} holds where that is written down, or empty where it is
     * not.
     *
     * <p>A text written down holds as many as its code points, counted as a run counts them. A list
     * written in the source holds as many as it was written with, however each was arrived at and
     * however many there are. Any other container holds as many as the walk writes out that are
     * there on every run ({@link #onEveryRun}) — one a step keeps on a condition that turns on the
     * run makes the count turn on it too, and one past the figure leaves it unwritten.
     */
    public static <E> OptionalLong sizeOf(Stood<E> container, Reading<E> reading) {
        Core value = Core.withoutStanding(container.value());
        if (value instanceof Core.Str text) {
            return OptionalLong.of(ScalarValues.count(text.value()));
        }
        if (value instanceof Core.ListLit written) {
            return OptionalLong.of(written.elements().size());
        }
        if (!(of(container, reading) instanceof Walked.Each<E>(List<Occurrence<E>> each))) {
            return OptionalLong.empty();
        }
        long there = 0;
        for (Occurrence<E> one : each) {
            Boolean kept = onEveryRun(one, reading);
            if (kept == null) {
                return OptionalLong.empty();
            }
            there += kept ? 1 : 0;
        }
        return OptionalLong.of(there);
    }

    /**
     * Whether {@code one} is there on every run: false where one truth it was kept by comes out the
     * other way on every run, whatever the others do; true where every one comes out the way it was
     * kept by on every run; and null where neither is so, one of them turning on the run.
     *
     * <p>Which arm of a choice a run takes is not folded here, so an occurrence kept by one turns
     * on the run.
     */
    static <E> Boolean onEveryRun(Occurrence<E> one, Reading<E> reading) {
        boolean decided = true;
        for (Kept<E> kept : one.keptWhere()) {
            switch (kept) {
                case Kept.ATruth<E>(Stood<E> truth, boolean wanted, int _) -> {
                    if (!(reading.folded(truth).orElse(null) instanceof Boolean holds)) {
                        decided = false;
                    } else if (holds != wanted) {
                        return false;
                    }
                }
                case Kept.AnArm<E> _ -> decided = false;
            }
        }
        return decided ? true : null;
    }

    /**
     * The element {@code List.get(index, list)} holds where it holds one, or null where which it is
     * is not one answer.
     *
     * <p>Where {@code option} stands as such a call, the index stands as a number written down and
     * the list is written out up to and including that element, with each of them there on every
     * run or on none ({@link #onEveryRun}). An element some step keeps on some runs and not others
     * moves every element after it, and is itself the one picked only where it is kept — so where
     * any of the elements up to and including the one picked turns on the run, nothing is said. One
     * there on no run moves nothing and is passed over. The list is written out that far and no
     * further, since the elements past the one picked move nothing.
     */
    public static <E> Occurrence<E> picked(Core option, E at, Reading<E> reading) {
        Stood<E> call = reading.standing(option, at);
        if (!(AnOperationApplied.of(call.value()) instanceof AnOperationApplied(
                ValueName.Stdlib.Operation operation, List<Core> args))
                || reading.symbols().kernelOf(operation) != Kernel.LIST_GET || args.size() != 2
                || !(Core.withoutStanding(reading.standing(args.get(0), call.at()).value())
                        instanceof Core.Int index)
                || index.value() < 0 || index.value() >= MOST_WALKED) {
            return null;
        }
        Stood<E> list = reading.standing(args.get(1), call.at());
        // As many as the index reaches, and as many again for each passed over on the way.
        int enough = (int) index.value() + 1;
        while (true) {
            if (!(of(list, reading, enough, new int[] {0})
                    instanceof Walked.Each<E>(List<Occurrence<E>> each))) {
                return null;
            }
            int left = (int) index.value();
            for (Occurrence<E> one : each) {
                Boolean there = onEveryRun(one, reading);
                if (there == null) {
                    return null;
                }
                if (there && left-- == 0) {
                    return one;
                }
            }
            if (each.size() < enough || enough >= MOST_WALKED) {
                return null;
            }
            enough = Math.min(MOST_WALKED, enough + left + 1);
        }
    }

    /** The first {@code enough} occurrences {@code container} holds, or every one where it holds
     *  fewer, counting into {@code walked}. */
    private static <E> Walked<E> of(Stood<E> container, Reading<E> reading, int enough,
                                    int[] walked) {
        E at = container.at();
        Core value = Core.withoutStanding(container.value());
        if (value instanceof Core.ListLit written) {
            List<Occurrence<E>> out = new ArrayList<>();
            for (Core each : written.elements()) {
                if (out.size() >= enough) {
                    break;
                }
                if (++walked[0] > MOST_WALKED) {
                    return new Walked.PastTheFigure<>();
                }
                // Which value each member is does not turn on the type it stands as in the list.
                out.add(Occurrence.always(new Stood<>(Core.withoutStanding(each), at)));
            }
            return new Walked.Each<>(out);
        }
        if (AnOperationApplied.of(value) instanceof AnOperationApplied(
                ValueName.Stdlib.Operation operation, List<Core> args)
                && reading.symbols().kernelOf(operation) == Kernel.STRING_CODE_POINTS
                && args.size() == 1) {
            return codePointsOf(reading.standing(args.getFirst(), at), value, enough, walked);
        }
        if (AnOperationApplied.of(value) instanceof AnOperationApplied(
                ValueName.Stdlib.Operation operation, List<Core> args)
                && reading.symbols().kernelOf(operation) == Kernel.LIST_RANGE_INCLUSIVE
                && args.size() == 2) {
            return rangeOf(args, value, at, reading, enough, walked);
        }
        // Each block the call's closures stand as, with where it was written: the step's body is
        // read there, under the element it is handed, and not where the call stands.
        Map<Core.Block, E> written = new IdentityHashMap<>();
        ElementBindings.PiecesOfEachElement pieces = ElementBindings.piecesOfEachElement(value,
                closure -> {
                    Stood<E> stood = reading.standing(closure, at);
                    if (!(Core.withoutStanding(stood.value()) instanceof Core.Block block)) {
                        return null;
                    }
                    written.put(block, stood.at());
                    return block;
                });
        if (pieces == null || pieces.element() == null || pieces.element().binding() == null) {
            Choice choice = Choice.of(value);
            return choice == null ? new Walked.NotWrittenOut<>()
                    : chosen(value, choice, at, reading, enough, walked);
        }
        E stepAt = written.getOrDefault(pieces.step(), at);
        // A map's and a filter's pieces are one to an element, so as many elements are enough; a
        // flatMap's are any number to an element, so its elements are walked until enough pieces
        // are.
        int ofTheSource = switch (pieces.piece()) {
            case THE_CLOSURES_ANSWER, THE_ELEMENT_WHERE_IT_HOLDS -> enough;
            case WHAT_THE_CLOSURE_ANSWERS -> Integer.MAX_VALUE;
        };
        Walked<E> from = of(reading.standing(pieces.walked(), at), reading, ofTheSource, walked);
        if (!(from instanceof Walked.Each<E>(List<Occurrence<E>> elements))) {
            return from;
        }
        BindingId element = pieces.element().binding();
        List<Occurrence<E>> out = new ArrayList<>();
        // Whether every element the step was handed so far was handed it on every run, which is
        // what makes the number of an application the number a run counts it as.
        boolean everyOneReached = true;
        for (int application = 0; application < elements.size(); application++) {
            Occurrence<E> each = elements.get(application);
            if (out.size() >= enough) {
                break;
            }
            everyOneReached &= each.keptWhere().isEmpty();
            // The step's body read on the application handing it this element.
            Stood<E> answered = new Stood<>(pieces.step().body(),
                    reading.handing(stepAt, element, each.value()));
            switch (pieces.piece()) {
                case THE_CLOSURES_ANSWER -> {
                    if (++walked[0] > MOST_WALKED) {
                        return new Walked.PastTheFigure<>();
                    }
                    out.add(new Occurrence<>(answered, each.keptWhere(),
                            everyOneReached ? OptionalInt.of(application) : OptionalInt.empty()));
                }
                case THE_ELEMENT_WHERE_IT_HOLDS -> {
                    if (++walked[0] > MOST_WALKED) {
                        return new Walked.PastTheFigure<>();
                    }
                    List<Kept<E>> kept = new ArrayList<>(each.keptWhere());
                    kept.add(new Kept.ATruth<>(answered, true, application));
                    out.add(new Occurrence<>(each.value(), kept, each.answered()));
                }
                case WHAT_THE_CLOSURE_ANSWERS -> {
                    Walked<E> inside = of(reading.standing(answered.value(), answered.at()),
                            reading, enough - out.size(), walked);
                    if (!(inside instanceof Walked.Each<E>(List<Occurrence<E>> made))) {
                        return inside;
                    }
                    made.forEach(one -> out.add(one.keptAlsoWhere(each.keptWhere())));
                }
            }
        }
        return new Walked.Each<>(out);
    }

    /**
     * The occurrences each arm of {@code choice}, which {@code fork} is, answers — the arms in the
     * order {@link Choice} numbers them, each read where its arm is entered and kept where it is
     * taken.
     *
     * <p>Every arm walked or nothing: an arm this cannot write out holds elements a run taking it
     * walks, so the others alone are not every element the container may hold. The arms past the
     * first {@code enough} occurrences are not walked, as the elements past them are not by any
     * other step of this walk: what is asked for is the first ones. What taking an arm states
     * is not said here, however the arm is decided: it is a fact of the whole fork, and its reader
     * is the reader of conditions.
     */
    private static <E> Walked<E> chosen(Core fork, Choice choice, E at, Reading<E> reading,
                                        int enough, int[] walked) {
        List<Occurrence<E>> out = new ArrayList<>();
        for (int part = 0; part < choice.arms().size() && out.size() < enough; part++) {
            Choice.Arm arm = choice.arms().get(part);
            Kept<E> taken = new Kept.AnArm<>(new Stood<>(fork, at), part);
            Walked<E> inside = of(reading.standing(arm.answers(),
                    reading.choosing(at, arm.decidedBy())), reading, enough - out.size(), walked);
            if (!(inside instanceof Walked.Each<E>(List<Occurrence<E>> made))) {
                return inside;
            }
            made.forEach(one -> out.add(one.keptAlsoWhere(List.of(taken))));
        }
        return new Walked.Each<>(out);
    }

    /**
     * The numbers {@code List.rangeInclusive(from, to)} holds, from {@code from} up to and
     * including {@code to}, where both stand as numbers written down — none where {@code from} is
     * past {@code to}, and nothing written out where either turns on the run.
     */
    private static <E> Walked<E> rangeOf(List<Core> bounds, Core call, E at, Reading<E> reading,
                                         int enough, int[] walked) {
        if (!(reading.folded(reading.standing(bounds.get(0), at)).orElse(null) instanceof Long from)
                || !(reading.folded(reading.standing(bounds.get(1), at)).orElse(null)
                        instanceof Long to)) {
            return new Walked.NotWrittenOut<>();
        }
        List<Occurrence<E>> out = new ArrayList<>();
        // The span is never subtracted, so one no long holds stops at the figure and not at an
        // overflow.
        for (long each = from; each <= to && out.size() < enough; each++) {
            if (++walked[0] > MOST_WALKED) {
                return new Walked.PastTheFigure<>();
            }
            out.add(Occurrence.always(new Stood<>(new Core.Int(each, Type.INT, call.pos()), at)));
            if (each == Long.MAX_VALUE) {
                break;
            }
        }
        return new Walked.Each<>(out);
    }

    /** The code points of the text {@code text} stands as ({@link WrittenCodePoints}), or nothing
     *  written out where it is not one written down. */
    private static <E> Walked<E> codePointsOf(Stood<E> text, Core call, int enough,
                                              int[] walked) {
        if (!(Core.withoutStanding(text.value()) instanceof Core.Str written)) {
            return new Walked.NotWrittenOut<>();
        }
        List<Occurrence<E>> out = new ArrayList<>();
        for (Core each : WrittenCodePoints.of(written.value(), Math.min(enough, MOST_WALKED + 1),
                call.pos())) {
            if (++walked[0] > MOST_WALKED) {
                return new Walked.PastTheFigure<>();
            }
            out.add(Occurrence.always(new Stood<>(each, text.at())));
        }
        return new Walked.Each<>(out);
    }
}
