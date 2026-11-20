package souther.compiler.partition;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.AConstructionStopShown;
import souther.compiler.inputs.AStopShown;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.WhatAConstructionAsks;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Whether a run on the way to a comparison stops at each construction on the way that asks
 * something of it: shown not to, shown to, or neither — what {@link StopAssessment} answers of an
 * operation, answered of what a construction asks.
 *
 * <p>{@link Judgement.Safe} is a proof that every run taking the way to the comparison and getting
 * to the construction meets what it asks: the way holds it, or a construction every such run has
 * got past by then asks as much. {@link Judgement.Stops} is a proof that some run does not, and
 * rests on one value of the input that exists ({@link AValueOfTheInput}), meets every condition on
 * the way to the comparison, gets to the construction with nothing before it ending the run, and
 * does not meet what it asks. {@link Judgement.Unresolved} is everything else.
 *
 * <p>Getting to it is shown where every run that takes the arms the way to the comparison takes
 * works the construction out unless something before it ends the run
 * ({@link WhatARunWorksOutBeforeACount#workedOutBeforeAConstruction}), every condition on that way
 * is a relation of numbers of the input or settled, and everything a run may work out before it
 * ends no run whatever the input ({@link WhatARunMayEndFor}) or is a construction whose condition
 * is read over numbers of the input, which the value is then asked to meet. What a construction
 * asks is where making its type succeeds, and nothing narrower or wider
 * ({@link DeclaredBounds#whereMakingSucceeds}), so a value meeting it gets
 * past the construction and one that does not stops there.
 *
 * <p>Asked of the way to the comparison, as what is said of the construction is said of the rule:
 * a run that does not take that way is a run to some other rule.
 *
 * <p>Asked of the constructions whose condition the reading of the way read
 * ({@link ComparisonReadings.Reading#asks}), and of no other. A construction on an arm of a value
 * worked out before the rule is none of those, and nothing here says of it either way: that no
 * finding names a construction is not that no run stops there.
 */
final class ConstructionStopAssessment {

    private ConstructionStopAssessment() {}

    /** How many values of the input are put to the proof of one construction before it is left
     *  unresolved: as many as a search for an assignment on the way tries of one position. */
    private static final int MOST_VALUES_TRIED =
            CompositionBudget.VALUES_A_POSITION_ON_THE_WAY_IS_TRIED_AT.maximum();

    /** What is shown of one construction. */
    sealed interface Judgement {

        /** Every run getting to it meets what it asks; nothing is said of it. */
        record Safe(ConstructionAsk ask) implements Judgement {}

        /** Some run on the way stops at the construction {@code shown} names. */
        record Stops(Shown shown) implements Judgement {}

        /** Neither is shown, and {@code told} is what it asks that the way does not hold. */
        record Unresolved(WhatAConstructionAsks told) implements Judgement {}
    }

    /**
     * That a run on the way stops at a construction: the value of the input {@link #at}, a whole
     * number at each place it is asked of, exists, takes the way, gets to the construction and does
     * not meet what it asks ({@link #told}). Made here and nowhere else, and only once all of that
     * is shown.
     */
    static final class Shown {

        private final WhatAConstructionAsks told;
        private final Map<NumericTerm, ExactRatio> at;

        private Shown(WhatAConstructionAsks told, Map<NumericTerm, ExactRatio> at) {
            this.told = told;
            this.at = Map.copyOf(at);
        }

        WhatAConstructionAsks told() {
            return told;
        }

        Map<NumericTerm, ExactRatio> at() {
            return at;
        }

        @Override
        public String toString() {
            return told.construction() + " at " + told.at() + " for " + at;
        }
    }

    /**
     * What is shown of each of {@code asked}, constructions on the way to the comparison
     * {@code each} reads, where the way to it holds what {@code heldOnTheWay} says: in the order
     * they are asked.
     */
    static List<Judgement> of(ComparisonReadings.Reading each, List<ConstructionAsk> asked,
                              Predicate<Proposition> heldOnTheWay,
                              InputReading read) {
        List<Judgement> out = new ArrayList<>();
        // Whether the way holds a part is asked of each part once, however many times it is read.
        Map<Proposition, Boolean> held = new HashMap<>();
        Predicate<Proposition> onTheWay = part -> held.computeIfAbsent(part, heldOnTheWay::test);
        for (ConstructionAsk ask : asked) {
            // What asks nothing, or nothing the way does not hold, is safe whatever the tree says,
            // and the tree is walked only for what is left.
            if (ask.toldOf(is -> onTheWay.test(is.read())).isEmpty()) {
                out.add(new Judgement.Safe(ask));
                continue;
            }
            Optional<WhatARunWorksOutBeforeACount.BeforeAConstruction> before =
                    each.workedOutBefore(ask.made());
            List<ConstructionAsk.Requirement.Is> gotPast = before
                    .map(it -> gotPast(it.onEveryRun(), each.asks(), ask)).orElse(List.of());
            Optional<WhatAConstructionAsks> told = ask.toldOf(is -> onTheWay.test(is.read())
                    || (is.exact() != null && gotPast.stream()
                            .anyMatch(past -> past.exact().implies(is.exact()))));
            if (told.isEmpty()) {
                out.add(new Judgement.Safe(ask));
                continue;
            }
            Shown shown = before.map(it -> aStopAt(each, ask, told.get(), it, read)).orElse(null);
            out.add(shown != null ? new Judgement.Stops(shown)
                    : new Judgement.Unresolved(told.get()));
        }
        return out;
    }

    /** What {@code judged} leave unresolved, as a finding says it, in the order judged. */
    static List<WhatAConstructionAsks> notShown(List<Judgement> judged) {
        List<WhatAConstructionAsks> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Unresolved(WhatAConstructionAsks told)) {
                out.add(told);
            }
        }
        return out;
    }

    /**
     * What shows a run on the way stops at a construction, as a finding says it: what it asks and
     * the number the value of the input holds at each place, in the order the input {@code read}
     * reads declares its places. Made from what was shown here and from nothing else.
     */
    static List<AConstructionStopShown> stopsShown(List<Judgement> judged, InputReading read) {
        List<AConstructionStopShown> out = new ArrayList<>();
        for (Judgement each : judged) {
            if (each instanceof Judgement.Stops(Shown shown)) {
                List<AStopShown.NumberAt> at = new ArrayList<>();
                for (Position place : read.domain().positions()) {
                    ExactRatio held = shown.at().get(new NumericTerm.ValueOf(place.path()));
                    if (held != null) {
                        at.add(new AStopShown.NumberAt(place.path(), held.floor().orNull()));
                    }
                }
                out.add(new AConstructionStopShown(shown.told(), at));
            }
        }
        return out;
    }

    /**
     * What every run that gets to {@code ask}'s construction has met by then, of what the
     * constructions among {@code asks} it has got past ask: each part of a condition that holds
     * wherever the condition does, of every construction the parts in {@code onEveryRun} work out
     * whenever they run, read over numbers of the input.
     *
     * <p>A run that got here worked each of those out and was not ended by it, and a construction
     * whose type refuses what it is handed ends the run — so it was built, and what it asks holds.
     * That rests on a step being a value a run gets past or stops at, which is what
     * {@link Evaluated#inOrder} lists: the construction an attempt tests, which takes the other arm
     * where it is refused, is the attempt's deciding and no step of it.
     */
    private static List<ConstructionAsk.Requirement.Is> gotPast(List<Core> onEveryRun,
                                                               List<ConstructionAsk> asks,
                                                               ConstructionAsk ask) {
        List<ConstructionAsk.Requirement.Is> out = new ArrayList<>();
        for (ConstructionAsk other : asks) {
            if (other.made() == ask.made()) {
                continue;
            }
            boolean passed = onEveryRun.stream()
                    .anyMatch(part -> Evaluated.runsWhenever(part, other.made()));
            if (passed) {
                other.requirement().heldWhereItIs().stream()
                        .filter(is -> is.exact() != null).forEach(out::add);
            }
        }
        return out;
    }

    /**
     * That a run on the way to the comparison stops at {@code ask}'s construction, or null where
     * that is not shown: everything a run may work out first is asked whether it may end the run,
     * the way whether it is read, and only where all of that is answered is a value looked for.
     */
    private static Shown aStopAt(ComparisonReadings.Reading each, ConstructionAsk ask,
                                 WhatAConstructionAsks told,
                                 WhatARunWorksOutBeforeACount.BeforeAConstruction before,
                                 InputReading read) {
        List<ConstructionAsk> first = new ArrayList<>();
        for (Core part : before.onSomeRun()) {
            if (!getsPast(part, each.asks(), first)) {
                return null;
            }
        }
        List<TakenConstraint.Affine> way = new ArrayList<>();
        for (OnTheWay entry : each.assumed()) {
            if (entry instanceof OnTheWay.TakenIn(var _,
                    RowDemand.Relational(TakenConstraint.Affine affine), var _, var _)) {
                way.add(affine);
            } else if (!(entry instanceof OnTheWay.Settled(var _, var _, boolean thisWay)
                    && thisWay)) {
                return null;
            }
        }
        List<LinearForm<NumericTerm>> forms = new ArrayList<>();
        way.forEach(it -> forms.add(it.form()));
        for (ConstructionAsk one : first) {
            formsOf(one.requirement(), forms);
        }
        formsOf(ask.requirement(), forms);
        Set<NumericTerm> numbers = new LinkedHashSet<>();
        for (LinearForm<NumericTerm> form : forms) {
            if (!numbersOf(form, numbers)) {
                return null;
            }
        }
        Set<TermPath> places = new LinkedHashSet<>();
        for (NumericTerm number : numbers) {
            places.add(((NumericTerm.ValueOf) number).position());
        }
        if (!AValueOfTheInput.holdsAnyWholeNumbersAt(read, places)) {
            return null;
        }
        Map<NumericTerm, List<ExactRatio>> tried = new LinkedHashMap<>();
        for (NumericTerm number : numbers) {
            tried.put(number, valuesToTry(number, way, first, ask, read));
        }
        int[] left = {MOST_VALUES_TRIED};
        return tryingEach(List.copyOf(numbers), 0, new LinkedHashMap<>(), tried, left,
                values -> stopsAt(values, way, first, ask) ? new Shown(told, values) : null);
    }

    /**
     * Whether working {@code e} out, and everything under it, gets a run past it, the value
     * looked for meeting what {@code passed} ask: every node of it ends no run whatever the input,
     * or is a construction among {@code asks} whose condition is read over numbers of the input,
     * which is then added to {@code passed}. The construction an attempt tests takes the other arm
     * where it is refused, and ends nothing ({@link WhatARunMayEndFor#forEachWorkedOut}).
     */
    private static boolean getsPast(Core e, List<ConstructionAsk> asks,
                                    List<ConstructionAsk> passed) {
        Core node = Core.withoutStanding(e);
        if (node instanceof Core.IfConstructed attempt) {
            boolean[] all = {true};
            WhatARunMayEndFor.forEachWorkedOut(attempt,
                    (part, _) -> all[0] = all[0] && getsPast(part, asks, passed));
            return all[0];
        }
        for (Core each : Core.subexpressionsAt(node)) {
            if (Core.withoutStanding(each) instanceof Core.Construct) {
                ConstructionAsk known = asks.stream().filter(ask -> ask.of(each)).findFirst()
                        .orElse(null);
                if (known == null || !known.requirement().overTheInput()) {
                    return false;
                }
                passed.add(known);
            } else if (!WhatARunMayEndFor.itself(each).endsNone()) {
                return false;
            }
        }
        boolean[] all = {true};
        Core.forEachChild(node, child -> all[0] = all[0] && getsPast(child, asks, passed));
        return all[0];
    }

    /** Every form {@code requirement} stands on that is over numbers of the input, into
     *  {@code into}. */
    private static void formsOf(ConstructionAsk.Requirement requirement,
                                List<LinearForm<NumericTerm>> into) {
        switch (requirement) {
            case ConstructionAsk.Requirement.Always _, ConstructionAsk.Requirement.Never _ -> { }
            case ConstructionAsk.Requirement.Is is -> {
                if (is.exact() != null) {
                    into.add(is.exact().form());
                }
            }
            case ConstructionAsk.Requirement.AllOf all ->
                    all.parts().forEach(part -> formsOf(part, into));
            case ConstructionAsk.Requirement.OneOf one ->
                    one.parts().forEach(part -> formsOf(part, into));
        }
    }

    /** Whether every number {@code form} is over is a value at a place of the input, or a product
     *  of forms of such values, each added to {@code into}. */
    private static boolean numbersOf(LinearForm<NumericTerm> form, Set<NumericTerm> into) {
        for (NumericTerm term : form.coefs().keySet()) {
            switch (term) {
                case NumericTerm.ValueOf _ -> into.add(term);
                case NumericTerm.ProductOf product -> {
                    if (!numbersOf(product.one(), into) || !numbersOf(product.other(), into)) {
                        return false;
                    }
                }
                default -> {
                    return false;
                }
            }
        }
        return true;
    }

    /** Whether a condition holds at a value of the input, fails there, or the arithmetic cannot
     *  say. */
    private enum Met { HOLDS, FAILS, NOT_KNOWN }

    /**
     * Whether a run with the input's numbers at {@code at} takes {@code way}, meets what each of
     * {@code first} asks, and does not meet what {@code ask} asks: each worked out exactly, and
     * none of it shown where the arithmetic cannot say.
     */
    private static boolean stopsAt(Map<NumericTerm, ExactRatio> at,
                                   List<TakenConstraint.Affine> way,
                                   List<ConstructionAsk> first, ConstructionAsk ask) {
        for (TakenConstraint.Affine condition : way) {
            ExactRatio comes = valueOf(condition.form(), at);
            if (comes == null || !condition.rel().holds(comes.signum())) {
                return false;
            }
        }
        for (ConstructionAsk one : first) {
            if (met(one.requirement(), at) != Met.HOLDS) {
                return false;
            }
        }
        return met(ask.requirement(), at) == Met.FAILS;
    }

    /** Whether a value of the input with its numbers at {@code at} meets {@code requirement}. */
    private static Met met(ConstructionAsk.Requirement requirement,
                           Map<NumericTerm, ExactRatio> at) {
        return switch (requirement) {
            case ConstructionAsk.Requirement.Always _ -> Met.HOLDS;
            case ConstructionAsk.Requirement.Never _ -> Met.FAILS;
            case ConstructionAsk.Requirement.Is is -> {
                ExactRatio comes = is.exact() == null ? null : valueOf(is.exact().form(), at);
                if (comes == null) {
                    yield Met.NOT_KNOWN;
                }
                yield is.exact().rel().holds(Integer.signum(comes.compareTo(is.exact().against())))
                        ? Met.HOLDS : Met.FAILS;
            }
            case ConstructionAsk.Requirement.AllOf all -> {
                Met out = Met.HOLDS;
                for (ConstructionAsk.Requirement part : all.parts()) {
                    Met one = met(part, at);
                    if (one == Met.FAILS) {
                        yield Met.FAILS;
                    }
                    if (one == Met.NOT_KNOWN) {
                        out = Met.NOT_KNOWN;
                    }
                }
                yield out;
            }
            case ConstructionAsk.Requirement.OneOf one -> {
                Met out = Met.FAILS;
                for (ConstructionAsk.Requirement part : one.parts()) {
                    Met each = met(part, at);
                    if (each == Met.HOLDS) {
                        yield Met.HOLDS;
                    }
                    if (each == Met.NOT_KNOWN) {
                        out = Met.NOT_KNOWN;
                    }
                }
                yield out;
            }
        };
    }

    /** What {@code form} comes to with each number of the input at {@code at}, a product of two
     *  forms as the two multiplied; null where the arithmetic cannot say. */
    private static ExactRatio valueOf(LinearForm<NumericTerm> form,
                                      Map<NumericTerm, ExactRatio> at) {
        Map<NumericTerm, ExactRatio> values = new LinkedHashMap<>(at);
        for (NumericTerm term : form.coefs().keySet()) {
            if (term instanceof NumericTerm.ProductOf product) {
                ExactRatio one = valueOf(product.one(), at);
                ExactRatio other = valueOf(product.other(), at);
                if (one == null || other == null
                        || !(one.times(other) instanceof ExactAnswer.Held<ExactRatio>(
                                ExactRatio both))) {
                    return null;
                }
                values.put(term, both);
            }
        }
        return WholeValuesMeeting.valueOf(form, values);
    }

    /** What is asked of one value of every number. */
    @FunctionalInterface
    private interface Asking {
        Shown at(Map<NumericTerm, ExactRatio> values);
    }

    /** {@code ask} of each way of putting {@code numbers} from {@code from} on at the values tried
     *  for each, while {@code left} lasts, until it answers. */
    private static Shown tryingEach(List<NumericTerm> numbers, int from,
                                    Map<NumericTerm, ExactRatio> values,
                                    Map<NumericTerm, List<ExactRatio>> tried, int[] left,
                                    Asking ask) {
        if (from == numbers.size()) {
            if (left[0] <= 0) {
                return null;
            }
            left[0]--;
            return ask.at(values);
        }
        for (ExactRatio value : tried.get(numbers.get(from))) {
            values.put(numbers.get(from), value);
            Shown found = tryingEach(numbers, from + 1, values, tried, left, ask);
            if (found != null || left[0] <= 0) {
                return found;
            }
        }
        values.remove(numbers.get(from));
        return null;
    }

    /**
     * The values {@code number} is tried at: nought and one either side, the ends of its place, and
     * on both sides of where each condition over it alone turns — of the way, of what the
     * constructions before ask, and of what {@code ask} asks — each once, and none past the ends of
     * its place. Those at which a part of what {@code ask} asks over it alone is not met come
     * first, so that a value taking each number to the side the construction refuses is tried
     * before the budget is spent on the others.
     */
    private static List<ExactRatio> valuesToTry(NumericTerm number,
                                                List<TakenConstraint.Affine> way,
                                                List<ConstructionAsk> first,
                                                ConstructionAsk ask, InputReading read) {
        Set<ExactRatio> out = new LinkedHashSet<>();
        FormRange ends = FormRange.endsOf(number, read);
        for (long each : new long[] {0, 1, -1}) {
            out.add(ExactRatio.of(each));
        }
        if (ends != null) {
            out.add(ends.least());
            out.add(ends.greatest());
        }
        for (TakenConstraint.Affine condition : way) {
            turnsAt(number, condition.form(), ExactRatio.ZERO, out);
        }
        List<ConstructionAsk.Requirement> asked = new ArrayList<>();
        first.forEach(one -> asked.add(one.requirement()));
        asked.add(ask.requirement());
        for (ConstructionAsk.Requirement requirement : asked) {
            for (ConstructionAsk.Requirement.Is is : everyFormOf(requirement)) {
                if (is.exact() != null) {
                    turnsAt(number, is.exact().form(), is.exact().against(), out);
                }
            }
        }
        List<ExactRatio> within = out.stream().filter(each -> each.isWhole()
                && (ends == null || (each.compareTo(ends.least()) >= 0
                        && each.compareTo(ends.greatest()) <= 0))).toList();
        List<ExactRatio> refused = new ArrayList<>();
        List<ExactRatio> rest = new ArrayList<>();
        for (ExactRatio value : within) {
            boolean refusedThere = everyFormOf(ask.requirement()).stream().anyMatch(is ->
                    is.exact() != null && is.exact().form().coefs().keySet().equals(Set.of(number))
                            && met(is, Map.of(number, value)) == Met.FAILS);
            if (refusedThere) {
                refused.add(value);
            } else {
                rest.add(value);
            }
        }
        refused.addAll(rest);
        return refused;
    }

    /** Every form standing to a number in {@code requirement}, under every one of several and one
     *  of several alike. */
    private static List<ConstructionAsk.Requirement.Is> everyFormOf(
            ConstructionAsk.Requirement requirement) {
        return switch (requirement) {
            case ConstructionAsk.Requirement.Always _, ConstructionAsk.Requirement.Never _ ->
                    List.of();
            case ConstructionAsk.Requirement.Is is -> List.of(is);
            case ConstructionAsk.Requirement.AllOf all -> all.parts().stream()
                    .flatMap(part -> everyFormOf(part).stream()).toList();
            case ConstructionAsk.Requirement.OneOf one -> one.parts().stream()
                    .flatMap(part -> everyFormOf(part).stream()).toList();
        };
    }

    /** The whole numbers either side of where {@code form}, a form of {@code number} alone, comes
     *  to {@code against}, into {@code out}; nothing where it is of anything else. */
    private static void turnsAt(NumericTerm number, LinearForm<NumericTerm> form,
                                ExactRatio against, Set<ExactRatio> out) {
        Map<NumericTerm, ExactRatio> coefs = form.coefs();
        if (coefs.size() != 1 || !coefs.containsKey(number)
                || !(against.minus(form.constant()) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio wanting))
                || !(wanting.dividedBy(coefs.get(number)) instanceof ExactAnswer.Held<ExactRatio>(
                        ExactRatio turns))) {
            return;
        }
        BigInteger floor = turns.floor().orNull();
        BigInteger ceiling = turns.ceiling().orNull();
        if (floor == null || ceiling == null) {
            return;
        }
        for (BigInteger each : List.of(floor.subtract(BigInteger.ONE), floor, ceiling,
                ceiling.add(BigInteger.ONE))) {
            out.add(ExactRatio.of(each));
        }
    }
}
