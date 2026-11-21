package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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
 * whole numbers of the input or settled, what comes before the comparison only where none of it
 * ends a run whatever the input ({@link ComparisonReadings.Reading#nothingBeforeItEndsARun}), and
 * the operation only where it is worked out wherever the comparison is, and it and every other
 * operation the comparison may work out before it are forms of those numbers. Showing more moves an
 * answer from unresolved to one of the others, and changes what neither of them means.
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

        /** An operation of whole numbers, and where its answer stops being one. */
        record PastItsEnds(UndividedByARelation.IntOperation operation) implements Site {

            @Override
            public String written() {
                return UndividedByARelation.written(operation.form());
            }
        }

        /** A quotient, and where its divisor is nought ({@link AbortKind#DIVISION_BY_ZERO}). */
        record ByNought(LinearForm<NumericTerm> divisor) implements Site {

            @Override
            public String written() {
                return "division by " + UndividedByARelation.written(divisor);
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

        /** Neither is shown of {@code site}, or, where that is null, of a stop no site names. */
        record Unresolved(Site site, WhyAStopIsNotShown why) implements Judgement {}
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

        @Override
        public String toString() {
            return site.written() + " at " + at;
        }
    }

    /**
     * One place a comparison works something out, as the caller that knows its ways puts it.
     *
     * @param worked      what is worked out there, and on which arm or application
     * @param aRowArrives whether a row may arrive there
     * @param way         the way to it: the way to the comparison, with what the arm or the
     *                    application states put on it where that is put on the way
     */
    record Place(ComparisonReadings.Reading.WorkedOutAt worked, boolean aRowArrives,
                 List<OnTheWay> way) {

        Place {
            way = List.copyOf(way);
        }
    }

    /**
     * What is shown of every operation a run getting to {@code each} works out at {@code places},
     * and of what it works out where no operation is told; and, where a row may arrive where the
     * statement says a run stops on rows of its own ({@code onRowsOfTheStatement}), that this is
     * unresolved.
     */
    static List<Judgement> of(ComparisonReadings.Reading each, List<Place> places,
                              boolean onRowsOfTheStatement, InputReading read) {
        List<Judgement> out = new ArrayList<>();
        if (onRowsOfTheStatement) {
            out.add(new Judgement.Unresolved(null, WhyAStopIsNotShown.ON_ROWS_OF_THE_STATEMENT));
        }
        List<LinearForm<NumericTerm>> divisors = divisorsOf(each, read);
        List<LinearForm<NumericTerm>> known = divisors.stream().filter(Objects::nonNull).toList();
        for (Place place : places) {
            UndividedByARelation.Working working = place.worked().stops().operations();
            WhatAWayLeavesOfAValue left = place.aRowArrives()
                    ? WhatAWayLeavesOfAValue.along(read, place.way()) : null;
            if (left != null && working.aStopUntold()
                    && working.leavesUntoldBeyond(each.quotients())) {
                out.add(new Judgement.Unresolved(null, WhyAStopIsNotShown.NO_OPERATION_TOLD));
            }
            List<UndividedByARelation.IntOperation> operations = working.operations();
            for (int at = 0; at < operations.size(); at++) {
                Site site = new Site.PastItsEnds(operations.get(at));
                if (left == null) {
                    out.add(new Judgement.Safe(site, WhyNone.NOT_WORKED_OUT));
                } else if (left.keepsWithinItsType(operations.get(at))
                        || left.noRowTakesItPastItsEnds(operations.get(at))) {
                    out.add(new Judgement.Safe(site, WhyNone.WITHIN_ITS_ENDS));
                } else {
                    out.add(aStopIn(each, place, site, operations.get(at).origin().node(), known,
                            divisors, read));
                }
            }
        }
        out.addAll(divisionsOf(each, places, divisors, read));
        return out;
    }

    /**
     * What each quotient evaluating the comparison always works out is divided by, as a form of
     * the value at places of the input, in the order they are worked out; null where the divisor
     * is no such form. A quotient is kept in its place whether or not its divisor is read: one
     * worked out before another that stops it is one the other is not got to past, and what is not
     * read of it is not that it does not stop.
     */
    private static List<LinearForm<NumericTerm>> divisorsOf(ComparisonReadings.Reading each,
                                                            InputReading read) {
        List<LinearForm<NumericTerm>> out = new ArrayList<>();
        for (Core.Binary quotient : each.quotients()) {
            LinearForm<NumericTerm> form = AffineReading.formOf(quotient.right(), each.reads(),
                    read, new ElementsMet(), AffineReading.Unkept.EVERY_NAME_AFRESH);
            out.add(form != null && form.coefs().keySet().stream()
                    .allMatch(NumericTerm.ValueOf.class::isInstance) ? form : null);
        }
        return out;
    }

    /**
     * What is shown of each quotient the comparison always works out, which a run works out
     * wherever it evaluates the comparison and stops at where the divisor is nought. None stops
     * where the way to the comparison, at each place it is worked out, keeps the divisor from
     * nought. A stop is looked for where the comparison is worked out at one place, what is worked
     * out there is all told, and the quotients before it have a divisor that is a form of the
     * input's numbers and is not nought.
     */
    private static List<Judgement> divisionsOf(ComparisonReadings.Reading each,
                                               List<Place> places,
                                               List<LinearForm<NumericTerm>> divisors,
                                               InputReading read) {
        List<Judgement> out = new ArrayList<>();
        Place beside = new Place(new ComparisonReadings.Reading.WorkedOutAt(
                StopEvidence.ofWhatIsToldOf(UndividedByARelation.Working.NO_STOPS), null, null),
                true, each.assumed());
        List<Place> comparison = places.isEmpty() ? List.of(beside) : places;
        for (int at = 0; at < divisors.size(); at++) {
            LinearForm<NumericTerm> divisor = divisors.get(at);
            // A divisor that is no form of places of the input — a choice, a count or a total of
            // a container — is the stop of the owner of that quotient, which holds the rows to
            // where it answers ({@link QuotientByAValue.Read#answers}) and says what it says of
            // the rest: none is judged here, and none after it is shown past it.
            if (divisor == null) {
                continue;
            }
            Site site = new Site.ByNought(divisor);
            List<LinearForm<NumericTerm>> before = divisors.subList(0, at);
            // Wherever the comparison is worked out, along the way to it there.
            if (comparison.stream().allMatch(place -> {
                WhatAWayLeavesOfAValue left = place.aRowArrives()
                        ? WhatAWayLeavesOfAValue.along(read, place.way()) : null;
                return left == null || left.keepsAwayFromNought(divisor);
            })) {
                out.add(new Judgement.Safe(site, WhyNone.DIVISOR_AWAY_FROM_NOUGHT));
            } else if (places.size() > 1 || before.contains(null)) {
                out.add(new Judgement.Unresolved(site, before.contains(null)
                        ? WhyAStopIsNotShown.NOT_OVER_THE_INPUT
                        : WhyAStopIsNotShown.NOT_EVERY_OPERATION_TOLD));
            } else {
                out.add(aStopIn(each, comparison.getFirst(), site, each.quotients().get(at),
                        before, divisors, read));
            }
        }
        return out;
    }

    /** Whether some quotient the comparison always works out may have its divisor at nought: a run
     *  is shown to stop there, or is not shown not to. What the rows that get past it leave of
     *  the numbers says nothing of the divisor at nought. */
    static boolean mayDivideByNought(List<Judgement> judged) {
        return judged.stream().anyMatch(each -> each instanceof Judgement.Stops(Shown shown)
                ? shown.site() instanceof Site.ByNought
                : each instanceof Judgement.Unresolved(var site, var _)
                        && site instanceof Site.ByNought);
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
                    if (held != null) {
                        at.add(new AStopShown.NumberAt(place.path(), held.floor().orNull()));
                    }
                }
                out.add(new AStopShown(shown.site().written(), at));
            }
        }
        return out;
    }

    /** Each operation {@code judged} leave unresolved, as written, and why, in the order they were
     *  judged: none written where no operation names the stop. */
    static List<AStopNotShown> stopsNotShown(List<Judgement> judged) {
        List<AStopNotShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Unresolved(var site, WhyAStopIsNotShown why)) {
                out.add(new AStopNotShown(Optional.ofNullable(site).map(Site::written), why));
            }
        }
        return out;
    }

    /**
     * That a run stops at {@code site}, one of what {@code place} works out, or why that is not
     * shown. Where it is worked out, how the way gets there and what is worked out before it are
     * asked first, and a value is looked for only where all of them are answered.
     */
    private static Judgement aStopIn(ComparisonReadings.Reading each, Place place, Site site,
                                     Core siteNode, List<LinearForm<NumericTerm>> quotients,
                                     List<LinearForm<NumericTerm>> divisors, InputReading read) {
        UndividedByARelation.Working working = place.worked().stops().operations();
        if (place.worked().madeWhere() != null) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.ON_AN_APPLICATION);
        }
        if (place.worked().onAnArm() != null) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.ON_AN_ARM);
        }
        // A working is not on every run where the expression the comparison was stopped at may
        // end a run before the operations it tells. Where the operation's step has a place in the
        // order, what may end a run before it is every node of the comparison not known to come
        // after it, each asked what it ends a run for: that is what a run stopping at the
        // operation has to get past, and what is left untold after it is not asked. Where it has
        // none, what the working leaves untold is, wherever it is. A quotient is worked out
        // wherever the comparison is ({@link QuotientsEveryRunWorksOut}), and the stop of one that
        // is among those asked is not left untold: a witness is asked to get past it.
        boolean mayEndBefore = site instanceof Site.PastItsEnds && !working.onEveryRun();
        boolean prefixKnown = mayEndBefore && each.places().hasAPlace(siteNode);
        boolean leftUntold = prefixKnown
                ? !onlyWhatIsAskedMayEndARunBefore(each, working, siteNode)
                : working.leavesUntoldBeyond(each.quotients())
                        || (mayEndBefore && !onlyWhatIsAskedMayEndARunBefore(each, working,
                                siteNode));
        if (leftUntold) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_EVERY_OPERATION_TOLD);
        }
        // A quotient worked out after an operation is not got to where the run stops in the
        // operation, so its divisor is not asked to be away from nought. One worked out before it
        // is, and where what is worked out beside the stop may end a run before the operation, a
        // divisor that is no form of the input's numbers is one nothing says is got past.
        if (site instanceof Site.PastItsEnds) {
            quotients = quotientsAskedBefore(each, divisors, siteNode, mayEndBefore);
        }
        if (!each.nothingBeforeItEndsARun()) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.SOMETHING_BEFORE_IT_MAY_STOP);
        }
        List<TakenConstraint.Affine> way = new ArrayList<>();
        for (OnTheWay entry : place.way()) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                way.add(affine);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.A_CONDITION_NOT_READ);
            }
        }
        // Everything else a run may work out before this: what this is not worked out before.
        // One worked out of this comes after it, and so does one the comparison works out past
        // everything of this; neither is got to where it stops. One whose place is not known is
        // asked.
        int at = site instanceof Site.PastItsEnds(var operation)
                ? indexOf(working.operations(), operation) : -1;
        List<UndividedByARelation.IntOperation> others = new ArrayList<>();
        for (int other = 0; other < working.operations().size(); other++) {
            UndividedByARelation.IntOperation it = working.operations().get(other);
            if (other != at && !it.after().contains(at)
                    && !each.places().comesAfter(it.origin().node(), siteNode)) {
                others.add(it);
            }
        }
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        forms.add(switch (site) {
            case Site.PastItsEnds(var operation) -> operation.overTheInput();
            case Site.ByNought(var divisor) -> divisor;
        });
        others.forEach(it -> forms.add(it.overTheInput()));
        forms.addAll(quotients);
        way.forEach(it -> forms.add(it.form()));
        Set<TermPath> places = new LinkedHashSet<>();
        for (LinearForm<NumericTerm> one : forms) {
            if (one == null) {
                return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
            }
            for (NumericTerm term : one.coefs().keySet()) {
                if (!(term instanceof NumericTerm.ValueOf(TermPath position))) {
                    return new Judgement.Unresolved(site, WhyAStopIsNotShown.NOT_OVER_THE_INPUT);
                }
                numbers.add(term);
                places.add(position);
            }
        }
        if (!AValueOfTheInput.holdsAnyWholeNumbersAt(read, places)) {
            return new Judgement.Unresolved(site, WhyAStopIsNotShown.NO_VALUE_SHOWN);
        }
        int[] left = {MOST_VALUES_TRIED};
        Before before = new Before(others, quotients, way);
        Shown shown = aValueItStopsAt(site, before, List.copyOf(numbers), read, left);
        if (shown != null) {
            return new Judgement.Stops(shown);
        }
        // Where the values ran out with the figure, more may be left untried, and that is said.
        return new Judgement.Unresolved(site, left[0] <= 0
                ? WhyAStopIsNotShown.NO_VALUE_FOUND_WITHIN_WHAT_IS_TRIED
                : WhyAStopIsNotShown.NO_VALUE_FOUND);
    }

    /**
     * The divisors of the quotients a run stopping at {@code siteNode} has worked out first: those
     * of the quotients not known to be worked out after it. A divisor that is no form of the
     * input's numbers is kept as null where {@code keepWhatIsNotRead}, which the caller reads as
     * a quotient nothing says is got past.
     */
    private static List<LinearForm<NumericTerm>> quotientsAskedBefore(
            ComparisonReadings.Reading each, List<LinearForm<NumericTerm>> divisors,
            Core siteNode, boolean keepWhatIsNotRead) {
        List<LinearForm<NumericTerm>> out = new ArrayList<>();
        for (int at = 0; at < divisors.size(); at++) {
            if (each.places().ownStepBefore(siteNode, each.quotients().get(at))) {
                continue;
            }
            if (divisors.get(at) != null || keepWhatIsNotRead) {
                out.add(divisors.get(at));
            }
        }
        return out;
    }

    /**
     * Whether, of what a run works out in the comparison before the step {@code siteNode} takes,
     * only what {@code working} tells or the comparison's quotients ask may end the run. A node
     * with no place is one that may be worked out before it. Where the comparison or the node is
     * not known, nothing is said.
     */
    private static boolean onlyWhatIsAskedMayEndARunBefore(ComparisonReadings.Reading each,
                                                           UndividedByARelation.Working working,
                                                           Core siteNode) {
        if (siteNode == null
                || !(each.statement() instanceof ComparisonReadings.Stated.AComparison(
                        var comparison))) {
            return false;
        }
        Set<Core> told = Collections.newSetFromMap(new IdentityHashMap<>());
        for (UndividedByARelation.IntOperation operation : working.operations()) {
            if (operation.origin().node() != null) {
                told.add(Core.withoutStanding(operation.origin().node()));
            }
        }
        told.add(Core.withoutStanding(siteNode));
        Set<Core> asked = Collections.newSetFromMap(new IdentityHashMap<>());
        each.quotients().forEach(quotient -> asked.add(Core.withoutStanding(quotient)));
        Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
        return onlyWhatIsAskedMayEndARunIn(comparison.left(), siteNode, each.places(), told,
                asked, met)
                && onlyWhatIsAskedMayEndARunIn(comparison.right(), siteNode, each.places(), told,
                asked, met);
    }

    private static boolean onlyWhatIsAskedMayEndARunIn(Core expression, Core siteNode,
                                                       EvaluationPlaces places, Set<Core> told,
                                                       Set<Core> asked, Set<Core> met) {
        Core node = Core.withoutStanding(expression);
        if (!met.add(node)) {
            return true;
        }
        if (!places.ownStepBefore(siteNode, node)) {
            if (!(WhatARunMayEndFor.itself(node) instanceof WhatARunMayEndFor.Endings.Known(
                    AbortSet kinds))) {
                return false;
            }
            Set<AbortKind> left = new HashSet<>(kinds.kinds());
            if (told.contains(node)) {
                left.remove(AbortKind.REQUIRED_FORM_HAS_NO_PLACE);
            }
            if (asked.contains(node)) {
                left.clear();
            }
            if (!left.isEmpty()) {
                return false;
            }
        }
        boolean[] accounted = {true};
        Core.forEachChild(node, child -> {
            if (accounted[0]) {
                accounted[0] = onlyWhatIsAskedMayEndARunIn(child, siteNode, places, told, asked,
                        met);
            }
        });
        return accounted[0];
    }

    /** Where {@code operation} is among {@code operations}, by the object it is. */
    private static int indexOf(List<UndividedByARelation.IntOperation> operations,
                               UndividedByARelation.IntOperation operation) {
        for (int at = 0; at < operations.size(); at++) {
            if (operations.get(at) == operation) {
                return at;
            }
        }
        throw new IllegalArgumentException("an operation judged is one the working tells");
    }

    /**
     * What a run that stops at a site has got past before it: the conditions of the way, every
     * operation within its ends and every quotient with its divisor away from nought.
     */
    private record Before(List<UndividedByARelation.IntOperation> operations,
                          List<LinearForm<NumericTerm>> divisors,
                          List<TakenConstraint.Affine> way) {}

    /**
     * A value of the input's {@code numbers} on the way, getting past what is worked out
     * {@code before} and stopping at {@code site}, or null where none of those tried does. Each
     * number but one is tried at a few values — nought and one either side, the ends of its place,
     * and on both sides of where a condition on the way of it alone turns — and the one left is
     * put where it takes the operation just past an end, or the divisor to nought. Each value
     * tried spends one of {@code left}, and none is tried once it is spent.
     */
    private static Shown aValueItStopsAt(Site site, Before before, List<NumericTerm> numbers,
                                         InputReading read, int[] left) {
        LinearForm<NumericTerm> form = switch (site) {
            case Site.PastItsEnds(var operation) -> operation.overTheInput();
            case Site.ByNought(var divisor) -> divisor;
        };
        List<TakenConstraint.Affine> way = before.way();
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        for (NumericTerm number : numbers) {
            tried.put(number, valuesToTry(number, way, read));
        }
        // A form of no number comes to its constant whatever the input holds: what is looked for
        // is a value on the way.
        if (form.coefs().isEmpty()) {
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
            for (NumericTerm free : form.coefs().keySet()) {
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
                if (found != null || left[0] <= 0) {
                    return found;
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
                                    Map<NumericTerm, List<ExactRatio>> tried, int[] left,
                                    Asking ask) {
        if (from == rest.size()) {
            if (left[0] <= 0) {
                return null;
            }
            left[0]--;
            return ask.at(values);
        }
        for (ExactRatio value : tried.get(rest.get(from))) {
            values.put(rest.get(from), value);
            Shown found = tryingEach(rest, from + 1, values, tried, left, ask);
            if (found != null || left[0] <= 0) {
                return found;
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
        return switch (site) {
            case Site.PastItsEnds(var operation) -> {
                ExactRatio comes = WholeValuesMeeting.valueOf(operation.overTheInput(), at);
                yield comes != null && !withinItsEnds(comes, operation);
            }
            case Site.ByNought(var divisor) -> {
                ExactRatio comes = WholeValuesMeeting.valueOf(divisor, at);
                yield comes != null && comes.signum() == 0;
            }
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
        return out.stream().filter(each -> ends == null || within(each, ends)).toList();
    }
}
