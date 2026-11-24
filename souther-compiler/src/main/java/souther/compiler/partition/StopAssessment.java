package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.check.StopOrigin;
import souther.compiler.core.Core;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.InputFact;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Whether a run stops in each operation a comparison works out: shown not to, shown to, or
 * neither.
 *
 * <p>Three answers, each with what shows it. {@link Judgement.Safe} is a proof that no run getting
 * to the operation stops in it, and may rest on what the way leaves a number, which holds every
 * row that arrives and more. {@link Judgement.Stops} is a proof that some run does, and rests on
 * one value of the input that exists, is on the way to the operation, has nothing before it end
 * the run, and works the operation out exactly past its ends: what the way leaves may hold rows
 * that never arrive, so it is where a value is looked for and never what shows one is there.
 * {@link Judgement.Unresolved} is everything else, with why. A comparison may hold all three.
 *
 * <p>A stop is shown only where every part of that is answered whole by an owner of it, and is
 * left unresolved otherwise: a value of the input only where its types state nothing of their
 * values ({@link AValueOfTheInput}), the way only where every condition on it is a relation of
 * whole numbers of the input or settled, what comes before the comparison only where every
 * operation of what may end a run there is told ({@link ComparisonReadings.Reading#workedOutBeforeIt}),
 * and the operation only where it is worked out wherever the comparison is. It and every other
 * operation a run may work out before it, there or before the comparison, are forms of those
 * numbers, but for one every value on the way keeps within its ends: the value looked for is one
 * of those, and gets past it. Showing more moves an answer from unresolved to one of the others,
 * and changes what neither of them means.
 *
 * <p>A value shown to stop a run is held against every operation judged kept within its ends on
 * the way it is on: one it takes past them is the two answers contradicting each other, and is
 * refused, never settled by taking one of them.
 */
final class StopAssessment {

    private StopAssessment() {}

    /** How many values of the input are put to the proof of one operation before it is left
     *  unresolved: as many as a search for an assignment on the way tries of one position. */
    private static final int MOST_VALUES_TRIED =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /** Why no run stops in an operation, where that is shown. */
    enum WhyNone {
        /** No row arrives where it is worked out. */
        NOT_WORKED_OUT,
        /** Every row the way leaves keeps it within its ends. */
        WITHIN_ITS_ENDS,
        /** Every row the way leaves keeps the divisor away from nought. */
        DIVISOR_AWAY_FROM_NOUGHT
    }

    /**
     * Where a run may stop in working something out: an operation whose answer may lie past the
     * ends of its type, or a quotient whose divisor may be nought. The first stops where the
     * answer is outside its ends and the second where an operand is outside what the operation is
     * defined on, so neither is said as the other.
     */
    sealed interface Site {

        /** What is worked out there, as a finding writes it. */
        String written();

        /**
         * Whether a run stopping at {@code other} stops in what this is, as a finding says it:
         * what is shown of a site is that a run stops in it as written, for its kind of stop, at
         * a value, and not at which place writing it a run stops first. A value that takes this
         * past where it stops takes such another past where it stops, or lets it by, so a run
         * with it stops in this wherever it stops first; one is not asked to get past the other.
         */
        boolean sameStopAs(Site other);

        /**
         * An operation of whole numbers, and where its answer stops being one. Another is the
         * same stop where it is written as this is and stops for the same kind of end: where its
         * type stops, or where a construction's clauses leave it.
         *
         * <p>Whatever ends each is held to: that is not the same telling
         * ({@link UndividedByARelation.IntOperation#sameOperationAs}), which is a question of what
         * was told and not of where a run stops. One with narrower ends that a value takes past
         * them stops a run in this as written before this is got to; one with wider ends lets the
         * value by to this. Two such are told of one place in a model: a date moved and read
         * again by its year is told held to the calendar's days and once more held to the days
         * of the years it counts, which end a day apart.
         */
        record PastItsEnds(UndividedByARelation.IntOperation operation) implements Site {

            @Override
            public String written() {
                return UndividedByARelation.written(operation.form());
            }

            @Override
            public boolean sameStopAs(Site other) {
                return other instanceof PastItsEnds(var that)
                        && that.form().equals(operation.form())
                        && that.ofTheRepresentation() == operation.ofTheRepresentation();
            }
        }

        /** A quotient, and where its divisor is nought ({@link AbortKind#DIVISION_BY_ZERO}).
         *  Another is the same stop where it divides by what this does. */
        record ByNought(LinearForm<NumericTerm> divisor) implements Site {

            @Override
            public String written() {
                return "division by " + UndividedByARelation.written(divisor);
            }

            @Override
            public boolean sameStopAs(Site other) {
                return other instanceof ByNought(var that) && that.equals(divisor);
            }
        }
    }

    /** What is shown of one place a run may stop, or of what a run works out where no site is
     *  told. */
    sealed interface Judgement {

        /** No run stops at {@code site}. */
        record Safe(Site site, WhyNone why) implements Judgement {}

        /** Some run stops at the site {@code shown} names. */
        record Stops(Shown shown) implements Judgement {}

        /**
         * Neither is shown of {@code site}, or, where that is null, of a stop no site names; and
         * {@code restsOn}, where the first stop left untold that it rests on is, where a reading
         * found it.
         */
        record Unresolved(Site site, WhyAStopIsNotShown why, Optional<StopOrigin> restsOn)
                implements Judgement {

            public Unresolved(Site site, WhyAStopIsNotShown why) {
                this(site, why, Optional.empty());
            }
        }
    }

    /**
     * That a run stops at {@link #site}: the value of the input {@link #at}, a whole number at
     * each place it is asked of, exists, gets to the site, and works it out past its ends or with
     * its divisor at nought, as the site says. Made here and nowhere else, and only once all of
     * that is shown.
     */
    static final class Shown {

        private final Site site;
        private final Map<NumericTerm, ExactRatio> at;

        private Shown(Site site, Map<NumericTerm, ExactRatio> at) {
            this.site = site;
            this.at = Map.copyOf(at);
        }

        Site site() {
            return site;
        }

        Map<NumericTerm, ExactRatio> at() {
            return at;
        }

        /** The same value, shown of {@code written}: the site this one is, with each value a run
         *  works out it is over put as one way a row makes it, as it is written. */
        Shown ofTheSiteAsWritten(Site written) {
            return new Shown(written, at);
        }

        @Override
        public String toString() {
            return site.written() + " at " + at;
        }
    }

    /**
     * Whether {@code quotient}, with the names as {@code reads} has them, divides by a form of the
     * values at places of the input: a divisor that is a choice, a count or a total of a container
     * is the stop of the owner of that quotient, which holds the rows to where it answers
     * ({@link QuotientByAValue.Read#answers}).
     */
    static boolean dividesByAFormOfThePlaces(Core.Binary quotient, InputReads reads,
                                             InputReading read) {
        LinearForm<NumericTerm> form = AffineReading.formOf(quotient.right(), reads, read,
                new ElementsMet(), AffineReading.Unkept.EVERY_NAME_AFRESH);
        return form != null && ofThePlaces(form);
    }

    /** Whether every number {@code form} is over is the value at a place of the input, or the
     *  product of two forms of such values. */
    private static boolean ofThePlaces(LinearForm<NumericTerm> form) {
        return form.coefs().keySet().stream().allMatch(term ->
                term instanceof NumericTerm.ValueOf
                        || (term instanceof NumericTerm.ProductOf product
                                && ofThePlaces(product.one()) && ofThePlaces(product.other())));
    }

    /**
     * What shows a run stops in what {@code judged} are of, as a finding says it: each stop shown,
     * its operation as written and the number the value of the input holds at each place, in the
     * order the input {@code read} reads declares its places. Made from what was shown here and
     * from nothing else, so a finding that a run stops is said only where this compiler has shown
     * one does.
     */
    static List<AStopShown> stopsShown(List<Judgement> judged, InputReading read) {
        List<AStopShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Stops(Shown shown)) {
                List<AStopShown.NumberAt> at = new ArrayList<>();
                for (Position place : read.domain().positions()) {
                    ExactRatio held = shown.at().get(new NumericTerm.ValueOf(place.path()));
                    if (held != null && !AValueOfTheInput.ofTheOnlyElement(place.path())) {
                        at.add(new AStopShown.NumberAt(place.path(), held.floor().orNull()));
                    }
                }
                List<InputFact> structure = new ArrayList<>();
                shown.at().forEach((term, held) -> {
                    if (term instanceof NumericTerm.TakenOf count
                            && AValueOfTheInput.howManyItHolds(count)) {
                        structure.add(new InputFact.ListLength(count.position(),
                                held.floor().orNull().intValueExact()));
                    } else if (term instanceof NumericTerm.ValueOf(TermPath place)
                            && AValueOfTheInput.ofTheOnlyElement(place)) {
                        structure.add(new InputFact.ListElement(
                                place.prefix(place.steps().size() - 1), 0, held.floor().orNull()));
                    }
                });
                structure.sort(InputFact.IN_A_STEADY_ORDER);
                out.add(new AStopShown(shown.site().written(), at, structure));
            }
        }
        return out;
    }

    /** Each operation {@code judged} leave unresolved, as written, and why, in the order they were
     *  judged: none written where no operation names the stop, and where the stops left untold
     *  that it rests on are. */
    static List<AStopNotShown> stopsNotShown(List<Judgement> judged) {
        List<AStopNotShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Unresolved(var site, WhyAStopIsNotShown why,
                    var restsOn)) {
                out.add(new AStopNotShown(Optional.ofNullable(site).map(Site::written), why,
                        restsOn));
            }
        }
        return out;
    }

    /** How many ways a way of several alternatives is read as ({@link #asWaysOfRelations})
     *  before the rest are left: a value is looked for along each, so as many as a search for an
     *  assignment on the way tries of one position. */
    static final int MOST_WAYS_OF_ALTERNATIVES =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /**
     * {@code way} as each way of relations of numbers of the input a value on it may meet, a
     * condition that came out one of several ways ({@link OnTheWay.OneOf}) read as each of them
     * in turn, and every other entry as {@link #asRelations} reads it: as many as
     * {@link #MOST_WAYS_OF_ALTERNATIVES}. Null where some entry is not read so; a way not made for
     * the figure is said by {@code left}.
     */
    static List<List<TakenConstraint.Affine>> asWaysOfRelations(List<OnTheWay> way,
                                                                boolean[] left) {
        List<List<TakenConstraint.Affine>> out = new ArrayList<>();
        return waysOfRelations(way, 0, new ArrayList<>(), out, left, false) ? out : null;
    }

    /**
     * The same, each entry not read as relations left out: what a value on the way meets at
     * least, for a reader asking where a run on it may not go, which a way holding less leaves
     * wider and never narrower. A way left unmade for the figure is said by {@code left}.
     */
    static List<List<TakenConstraint.Affine>> asWaysOfRelationsAtLeast(List<OnTheWay> way,
                                                                       boolean[] left) {
        List<List<TakenConstraint.Affine>> out = new ArrayList<>();
        waysOfRelations(way, 0, new ArrayList<>(), out, left, true);
        return out;
    }

    private static boolean waysOfRelations(List<OnTheWay> way, int at,
                                           List<TakenConstraint.Affine> sofar,
                                           List<List<TakenConstraint.Affine>> out,
                                           boolean[] left, boolean leavingOutWhatIsNotRead) {
        // Past the figure nothing more is made, and nothing more is looked at to make it.
        if (left[0]) {
            return true;
        }
        if (at == way.size()) {
            if (out.size() >= MOST_WAYS_OF_ALTERNATIVES) {
                left[0] = true;
            } else {
                out.add(List.copyOf(sofar));
            }
            return true;
        }
        OnTheWay entry = way.get(at);
        if (entry instanceof OnTheWay.OneOf several) {
            for (List<OnTheWay> alternative : several.alternatives()) {
                List<OnTheWay> past = new ArrayList<>(alternative);
                past.addAll(way.subList(at + 1, way.size()));
                if (!waysOfRelations(past, 0, sofar, out, left, leavingOutWhatIsNotRead)) {
                    return false;
                }
            }
            return true;
        }
        List<TakenConstraint.Affine> one = asRelations(List.of(entry));
        if (one == null) {
            if (!leavingOutWhatIsNotRead) {
                return false;
            }
            one = List.of();
        }
        int mark = sofar.size();
        sofar.addAll(one);
        try {
            return waysOfRelations(way, at + 1, sofar, out, left, leavingOutWhatIsNotRead);
        } finally {
            sofar.subList(mark, sofar.size()).clear();
        }
    }

    /**
     * {@code way} as the relations of numbers of the input a value on it meets, or null where a
     * condition of it is not one: each relation it takes in, each place a narrowing leaves a
     * position out of on its order, and nothing for a condition settled this way.
     */
    static List<TakenConstraint.Affine> asRelations(List<OnTheWay> way) {
        List<TakenConstraint.Affine> out = new ArrayList<>();
        for (OnTheWay entry : way) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                out.add(affine);
            } else if (entry instanceof OnTheWay.Narrowed narrowed
                    && aPlaceOnItsOrder(narrowed) instanceof List<TakenConstraint.Affine> holes) {
                out.addAll(holes);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return null;
            }
        }
        return out;
    }

    /**
     * That a run on {@code way} stops at {@code site}, or why that is not shown: a value of the
     * input meeting {@code way} is looked for that keeps each of {@code before} within its ends and
     * every divisor of {@code quotients} away from nought, and takes the site past where it stops.
     * One of {@code before} every value {@code left} leaves keeps within its ends is got past by
     * the value looked for, which is one of them, and is held against it once one is found.
     */
    static Judgement aStopLookedFor(Site site, List<UndividedByARelation.IntOperation> before,
                                    List<LinearForm<NumericTerm>> quotients,
                                    WhatAWayLeavesOfAValue left, List<TakenConstraint.Affine> way,
                                    InputReading read, Tries tries) {
        List<UndividedByARelation.IntOperation> others = new ArrayList<>(before);
        // One every value on the way keeps within its ends is got past by the value looked for,
        // which is one of them, and is not asked of it. That it is got past is held against the
        // value once one is found.
        List<UndividedByARelation.IntOperation> kept = others.stream()
                .filter(left::keepsWithinItsEnds).toList();
        others.removeAll(kept);
        // What the site is over, as numbers of the input: where it is over a value a run works out,
        // by each way a row makes that value come to a number, which a stop is looked for by in
        // turn.
        // One figure is spent for the whole site, whoever asks: every value tried is one unit of
        // it, and so is every way it is looked for by, along every way to the site. What a site
        // costs is no product of the ways and the values.
        List<Judgement> judged = new ArrayList<>();
        Attainment.Visitor lookFor = how -> {
            if (!tries.spend()) {
                return false;
            }
            Judgement one = aStopAttainedBy(how, site, others, quotients, kept, way, read, tries);
            judged.add(one);
            return !(one instanceof Judgement.Stops);
        };
        boolean everyWayMade = switch (site) {
            case Site.PastItsEnds(var operation) -> operation.forEachAttained(lookFor);
            case Site.ByNought(var divisor) -> {
                if (divisor != null) {
                    lookFor.wantsMore(Attainment.always(divisor));
                }
                yield true;
            }
        };
        // A way of a value that was not made for want of the figure is left undone as one not
        // visited is, and is said as that and not as a value no way is known for.
        if (!everyWayMade) {
            tries.leftSomethingUndone();
        }
        if (judged.isEmpty()) {
            return new Judgement.Unresolved(site, tries.cutShort()
                    ? WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                    : WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
        }
        Judgement last = judged.getLast();
        if (last instanceof Judgement.Stops) {
            return last;
        }
        // Where the figure ran out with ways or values left, more may be left untried, and that
        // is said.
        return tries.cutShort()
                ? new Judgement.Unresolved(site,
                        WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED)
                : judged.getFirst();
    }

    /**
     * The one figure a site is searched by ({@link #MOST_VALUES_TRIED}): every value tried is one
     * unit of it, and so is every way a stop is looked for by beyond the first, so what a site
     * costs is no product of the ways and the values.
     *
     * <p>Cut short is where a unit was asked for and there was none, and not where the last was
     * spent and the search was done: that a search used all it was given says nothing of whether
     * it left anything.
     */
    static final class Tries {

        private int left;
        private boolean refused;

        /** A site's figure. */
        Tries() {
            this(MOST_VALUES_TRIED);
        }

        /** Of {@code figure} units. */
        Tries(int figure) {
            this.left = figure;
        }

        /** Whether a unit is spent: one is, where there is one, and where there is none that is
         *  asked for and refused. */
        boolean spend() {
            if (left <= 0) {
                refused = true;
                return false;
            }
            left--;
            return true;
        }

        /** Whether none is left. */
        boolean spent() {
            return left <= 0;
        }

        /** That something was left undone for want of one. */
        void leftSomethingUndone() {
            refused = true;
        }

        boolean cutShort() {
            return refused;
        }
    }

    /**
     * That a run stops at {@code site}, which is over the numbers of the input as {@code how} says,
     * or why that is not shown: a value of the input is looked for that meets {@code way} and what
     * {@code how} holds, gets past {@code others} and {@code quotients}, and takes the site past
     * its ends. {@code kept} are what that value is then held against. Each value tried spends one
     * of {@code tries}, which the site as a whole is given.
     */
    private static Judgement aStopAttainedBy(Attainment how, Site site,
                                             List<UndividedByARelation.IntOperation> others,
                                             List<LinearForm<NumericTerm>> quotients,
                                             List<UndividedByARelation.IntOperation> kept,
                                             List<TakenConstraint.Affine> way, InputReading read,
                                             Tries tries) {
        List<TakenConstraint.Affine> holding = new ArrayList<>(way);
        holding.addAll(how.holding());
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        forms.add(how.form());
        others.forEach(it -> forms.add(it.overTheInput()));
        forms.addAll(quotients);
        holding.forEach(it -> forms.add(it.form()));
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        for (LinearForm<NumericTerm> one : forms) {
            if (one == null) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
            }
            numbers.addAll(one.coefs().keySet());
        }
        // A list's one element is a number of a list of one: how many it holds is asked beside it.
        for (NumericTerm term : List.copyOf(numbers)) {
            if (term instanceof NumericTerm.ValueOf(TermPath place)
                    && AValueOfTheInput.ofTheOnlyElement(place)) {
                NumericTerm count = AValueOfTheInput.howMany(
                        place.prefix(place.steps().size() - 1), read);
                if (count == null) {
                    return new Judgement.Unresolved(site, WhyAStopIsNotShown.NO_VALUE_SHOWN);
                }
                numbers.add(count);
            }
        }
        // A value of the input holding them exists where they meet what the input's declarations
        // ask of them, which the value looked for is asked to meet with the way.
        Optional<AValueOfTheInput.Meets> declared =
                AValueOfTheInput.whatAValueAtTheseTermsMeets(read, numbers);
        if (declared.isEmpty()) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.NO_VALUE_SHOWN);
        }
        holding.addAll(declared.get().constraints());
        Before before = new Before(how.form(), others, quotients, holding, declared.get());
        Shown shown = aValueItStopsAt(site, before, List.copyOf(numbers), read, tries);
        if (shown != null) {
            return new Judgement.Stops(againstWhatIsKept(shown, kept));
        }
        // Where the values ran out with the figure, more may be left untried, and that is said.
        return new Judgement.Unresolved(site, tries.cutShort()
                ? WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                : WhyAStopIsNotShown.NO_VALUE_FOUND);
    }

    /**
     * {@code shown}, held against {@code kept}, the operations judged to be kept within their ends
     * by every value on the way it is one of: each that the value works out comes out within them.
     * One that does not is the two judgements contradicting each other, which no answer here may
     * stand on, and is refused rather than one of them being taken.
     */
    private static Shown againstWhatIsKept(Shown shown,
                                           List<UndividedByARelation.IntOperation> kept) {
        for (UndividedByARelation.IntOperation each : kept) {
            ExactRatio comes = each.overTheInput() == null ? null
                    : WholeValuesMeeting.valueOf(each.overTheInput(), shown.at());
            if (comes != null && !withinItsEnds(comes, each)) {
                throw new IllegalStateException("a value shown to stop a run, " + shown
                        + ", takes " + each.form() + ", judged kept within its ends on the way,"
                        + " past them");
            }
        }
        return shown;
    }

    /**
     * A narrowing of a position to some of its cases, as what a value of it has to meet: where it
     * stands on its order is none of the places the narrowing leaves out, each a statement that
     * it is not there. Null where that is not all the narrowing asks — it asks of what a case
     * holds — or where the position is on no order, so that no place is left out.
     */
    private static List<TakenConstraint.Affine> aPlaceOnItsOrder(OnTheWay.Narrowed narrowed) {
        if (!narrowed.crossings().isEmpty() || narrowed.onItsOrder().isEmpty()) {
            return null;
        }
        List<TakenConstraint.Affine> out = new ArrayList<>();
        for (TakenConstraint.AwayFrom hole : narrowed.onItsOrder()) {
            if (!(hole.at() instanceof Count count)) {
                return null;
            }
            out.add(new TakenConstraint.Affine(new LinearForm<>(count.exactly().negated(),
                    Map.of(hole.term(), ExactRatio.ONE)), Rel.NE));
        }
        return out;
    }

    /**
     * What a run that stops at a site has got past before it: the conditions of the way, every
     * operation within its ends and every quotient with its divisor away from nought.
     *
     * @param site     what the site comes to, as numbers of the input: the form of the operation,
     *                 or of the divisor
     * @param declared what a value of the input holding the numbers has to meet: the way holds
     *                 its constraints, and its ties are asked of each value found
     */
    private record Before(LinearForm<NumericTerm> site,
                          List<UndividedByARelation.IntOperation> operations,
                          List<LinearForm<NumericTerm>> divisors,
                          List<TakenConstraint.Affine> way, AValueOfTheInput.Meets declared) {}

    /**
     * A value of the input's {@code numbers} on the way, getting past what is worked out
     * {@code before} and stopping at {@code site}, or null where none of those tried does. Each
     * number but one is tried at a few values — nought and one either side, the ends of its place,
     * and on both sides of where a condition on the way of it alone turns — and the one left is
     * put where it takes the operation just past an end, or the divisor to nought. Each value
     * tried spends one of {@code left}, and none is tried once it is spent.
     */
    private static Shown aValueItStopsAt(Site site, Before before, List<NumericTerm> numbers,
                                         InputReading read, Tries left) {
        LinearForm<NumericTerm> form = before.site();
        List<TakenConstraint.Affine> way = before.way();
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        for (NumericTerm number : numbers) {
            tried.put(number, valuesToTry(number, way, read));
        }
        // A form of no number comes to its constant whatever the input holds: it stops a run at
        // every value or at none, so that what is looked for is a value on the way, and only where
        // the constant is one the site stops at.
        if (form.coefs().isEmpty()) {
            if (!stopsAtTheSite(site, form.constant())) {
                return null;
            }
            return tryingEach(numbers, 0, new LinkedHashMap<>(), tried, left,
                    values -> stopsAt(site, before, values) ? new Shown(site, values) : null);
        }
        for (boolean above : new boolean[] {true, false}) {
            BigInteger past = switch (site) {
                case Site.PastItsEnds(var operation) -> above
                        ? operation.greatest().add(BigInteger.ONE)
                        : operation.least().subtract(BigInteger.ONE);
                case Site.ByNought _ -> BigInteger.ZERO;
            };
            List<NumericTerm> frees = List.copyOf(form.coefs().keySet());
            for (int which = 0; which < frees.size(); which++) {
                NumericTerm free = frees.get(which);
                List<NumericTerm> rest = numbers.stream().filter(each -> !each.equals(free))
                        .toList();
                Shown found = tryingEach(rest, 0, new LinkedHashMap<>(), tried, left, values -> {
                    ExactRatio put = whereItTakes(form, free, past, above, values);
                    FormRange ends = FormRange.endsOf(free, read);
                    if (put == null || ends == null || !within(put, ends)) {
                        return null;
                    }
                    Map<NumericTerm, ExactRatio> at = new LinkedHashMap<>(values);
                    at.put(free, put);
                    return stopsAt(site, before, at) ? new Shown(site, at) : null;
                });
                if (found != null) {
                    return found;
                }
                // Where the figure is spent with another number to put the value at, or the other
                // side of the ends to look at, those are left undone.
                if (left.spent()) {
                    if (which < frees.size() - 1 || above) {
                        left.leftSomethingUndone();
                    }
                    return null;
                }
            }
        }
        return null;
    }

    /** What is asked of one value of every number but one. */
    @FunctionalInterface
    private interface Asking {
        Shown at(Map<NumericTerm, ExactRatio> values);
    }

    /** {@code ask} of each way of putting {@code rest} from {@code from} on at the values tried
     *  for each, while {@code left} lasts, until it answers. */
    private static Shown tryingEach(List<NumericTerm> rest, int from,
                                    Map<NumericTerm, ExactRatio> values,
                                    Map<NumericTerm, List<ExactRatio>> tried, Tries left,
                                    Asking ask) {
        if (from == rest.size()) {
            return left.spend() ? ask.at(values) : null;
        }
        List<ExactRatio> tryAt = tried.get(rest.get(from));
        for (int at = 0; at < tryAt.size(); at++) {
            values.put(rest.get(from), tryAt.get(at));
            Shown found = tryingEach(rest, from + 1, values, tried, left, ask);
            if (found != null) {
                return found;
            }
            if (left.spent()) {
                if (at < tryAt.size() - 1) {
                    left.leftSomethingUndone();
                }
                return null;
            }
        }
        values.remove(rest.get(from));
        return null;
    }

    /**
     * The whole number {@code free} is put at for {@code form} to come to {@code past} or beyond
     * it, upwards where {@code above} and downwards otherwise, with every other number it is of at
     * {@code values}; null where the arithmetic cannot say.
     */
    private static ExactRatio whereItTakes(LinearForm<NumericTerm> form, NumericTerm free,
                                           BigInteger past, boolean above,
                                           Map<NumericTerm, ExactRatio> values) {
        Map<NumericTerm, ExactRatio> rest = new LinkedHashMap<>(form.coefs());
        ExactRatio weight = rest.remove(free);
        ExactRatio besides = WholeValuesMeeting.valueOf(new LinearForm<>(form.constant(), rest),
                values);
        if (besides == null
                || !(ExactRatio.of(past).minus(besides) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio wanting))
                || !(wanting.dividedBy(weight) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio at))) {
            return null;
        }
        BigInteger whole = (above == (weight.signum() > 0) ? at.ceiling() : at.floor()).orNull();
        return whole == null ? null : ExactRatio.of(whole);
    }

    /**
     * Whether a run with the input's numbers at {@code at} gets past what is worked out
     * {@code before}, every condition of the way, every operation within its ends and every
     * divisor not nought, and stops at {@code site}: each worked out exactly, and none of it shown
     * where the arithmetic cannot say.
     */
    private static boolean stopsAt(Site site, Before before, Map<NumericTerm, ExactRatio> at) {
        for (TakenConstraint.Affine condition : before.way()) {
            if (!WholeValuesMeeting.holdsAt(condition, at)) {
                return false;
            }
        }
        for (UndividedByARelation.IntOperation other : before.operations()) {
            ExactRatio comes = WholeValuesMeeting.valueOf(other.overTheInput(), at);
            if (comes == null || !withinItsEnds(comes, other)) {
                return false;
            }
        }
        for (LinearForm<NumericTerm> other : before.divisors()) {
            ExactRatio divisor = WholeValuesMeeting.valueOf(other, at);
            if (divisor == null || divisor.signum() == 0) {
                return false;
            }
        }
        ExactRatio comes = WholeValuesMeeting.valueOf(before.site(), at);
        return comes != null && stopsAtTheSite(site, comes) && before.declared().tiesHoldAt(at);
    }

    /** Whether a run that works {@code site} out as {@code comes} stops there: past the ends of
     *  its operation, or with the divisor at nought. */
    private static boolean stopsAtTheSite(Site site, ExactRatio comes) {
        return switch (site) {
            case Site.PastItsEnds(var operation) -> !withinItsEnds(comes, operation);
            case Site.ByNought _ -> comes.signum() == 0;
        };
    }

    private static boolean withinItsEnds(ExactRatio value,
                                         UndividedByARelation.IntOperation operation) {
        return value.compareTo(ExactRatio.of(operation.least())) >= 0
                && value.compareTo(ExactRatio.of(operation.greatest())) <= 0;
    }

    private static boolean within(ExactRatio value, FormRange ends) {
        return value.isWhole()
                && (ends.least() == null || value.compareTo(ends.least()) >= 0)
                && (ends.greatest() == null || value.compareTo(ends.greatest()) <= 0);
    }

    /**
     * The values {@code number} is tried at: nought and one either side, the ends of its place, and
     * on both sides of where each condition of {@code way} over it alone turns — each once, and
     * none past the ends of its place.
     */
    private static List<ExactRatio> valuesToTry(NumericTerm number,
                                                List<TakenConstraint.Affine> way,
                                                InputReading read) {
        Set<ExactRatio> out = new LinkedHashSet<>();
        FormRange ends = FormRange.endsOf(number, read);
        for (long each : new long[] {0, 1, -1}) {
            out.add(ExactRatio.of(each));
        }
        if (ends != null) {
            if (ends.least() != null) {
                out.add(ends.least());
            }
            if (ends.greatest() != null) {
                out.add(ends.greatest());
            }
        }
        for (TakenConstraint.Affine condition : way) {
            Map<NumericTerm, ExactRatio> coefs = condition.form().coefs();
            if (coefs.size() != 1 || !coefs.containsKey(number)
                    || !(condition.form().constant().negated()
                            .dividedBy(coefs.get(number))
                            instanceof ExactAnswer.Held<ExactRatio>(ExactRatio turns))) {
                continue;
            }
            BigInteger floor = turns.floor().orNull();
            BigInteger ceiling = turns.ceiling().orNull();
            if (floor == null || ceiling == null) {
                continue;
            }
            for (BigInteger each : List.of(floor.subtract(BigInteger.ONE), floor, ceiling,
                    ceiling.add(BigInteger.ONE))) {
                out.add(ExactRatio.of(each));
            }
        }
        return out.stream().filter(each -> ends == null || within(each, ends))
                .filter(each -> holdsOfItAlone(number, each, way)).toList();
    }

    /** Whether every condition of {@code way} over {@code number} alone holds with it at
     *  {@code value}: one that does not is a value no run on the way has, so it is not tried. */
    private static boolean holdsOfItAlone(NumericTerm number, ExactRatio value,
                                          List<TakenConstraint.Affine> way) {
        Map<NumericTerm, ExactRatio> at = Map.of(number, value);
        for (TakenConstraint.Affine condition : way) {
            Map<NumericTerm, ExactRatio> coefs = condition.form().coefs();
            if (coefs.size() == 1 && coefs.containsKey(number)
                    && !WholeValuesMeeting.holdsAt(condition, at)) {
                return false;
            }
        }
        return true;
    }
}
