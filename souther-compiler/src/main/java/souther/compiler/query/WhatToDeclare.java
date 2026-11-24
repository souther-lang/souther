package souther.compiler.query;

import souther.compiler.meaning.CaseExpansion;
import souther.compiler.partition.AChoiceReadThrough;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * What an author declares as behaviors so that some conditions of a body are read through no more
 * choices than are read of one condition.
 *
 * <p><b>Of the conditions it is asked of, and of no other.</b> Which conditions those are is the
 * asker's: before a measurement, the ones whose readings may come to more than are made
 * ({@link ConditionsReadThroughTooManyChoices}); after it, the ones that stopped
 * ({@link ConditionsStoppedAtAFigure}). What one condition is told is made of how its own values
 * are written, so a condition that was read whole suggests nothing for one that was not.
 *
 * <p><b>Two things take the choices out of a condition.</b> What a behavior answers is one value
 * to whoever calls it, so a helper declared as one leaves none of the choices written in it, or in
 * what it calls, for the condition to be read through. Where the helpers' choices are what comes
 * to too many readings, helpers are named. Where they are not — the choices written beside the
 * condition come to as many by themselves, or it is read on many elements and through no choice —
 * the condition is what is written in a behavior, handed what it compares.
 *
 * <p><b>No helper named can be left out.</b> Leaving one out, with the rest declared, leaves some
 * condition with more readings than are made of one. The ones in the fewest conditions are left
 * out first, so that one several share is kept before one for each of them, and of those the ones
 * that take the fewest readings out; so for a condition told of alone the helpers are the fewest
 * there are: a choice is taken out by one helper, the outermost around it that the condition is
 * not inside, so what is left is least where the greatest are taken out. For several they may not
 * be the fewest, and none of them is one that could be left out.
 *
 * @param conditions  how many conditions it is told of
 * @param helpers     the helpers to declare as behaviors, the one in the most conditions first
 * @param inABehavior how many of the conditions are themselves what is written in a behavior
 */
public record WhatToDeclare(int conditions, List<HelperToDeclare> helpers, int inABehavior) {

    /** Nothing is told of. */
    public static final WhatToDeclare NOTHING = new WhatToDeclare(0, List.of(), 0);

    public WhatToDeclare {
        helpers = List.copyOf(helpers);
        if (conditions > 0 && helpers.isEmpty() && inABehavior == 0) {
            throw new IllegalArgumentException("a condition is told of with something to do");
        }
    }

    /**
     * A helper to declare as a behavior.
     *
     * @param helper       the helper
     * @param conditions   how many of the conditions its choices are taken out of
     * @param calls        how many calls of it those conditions are read through
     * @param calledInside the helpers those calls are written inside, the nearest first: a helper
     *                     cannot call a behavior, so the calls move out of them, or they are
     *                     declared as behaviors as well
     */
    public record HelperToDeclare(ValueName.Helper helper, int conditions, int calls,
                                  List<ValueName.Helper> calledInside) {

        public HelperToDeclare {
            Objects.requireNonNull(helper, "some helper");
            calledInside = List.copyOf(calledInside);
        }
    }

    /** The readings a condition is left with where the helpers named are behaviors. */
    private static BigInteger left() {
        return BigInteger.valueOf(CompositionBudget.READINGS_OF_ONE_CONDITION.maximum());
    }

    /**
     * What is declared for {@code conditions}, each where {@code read} holds it: a condition the
     * walk of the body did not meet is read through no choice that walk said.
     */
    static WhatToDeclare of(Set<ModelOccurrence> conditions, List<AComparisonRead> read) {
        Map<ModelOccurrence, AComparisonRead> met = new LinkedHashMap<>();
        read.forEach(each -> met.merge(each.copy(), each, (one, other) ->
                readings(one.through()).compareTo(readings(other.through())) >= 0 ? one : other));
        List<Through> byHelpers = new ArrayList<>();
        for (ModelOccurrence each : conditions) {
            Through through = met.containsKey(each) ? Through.of(met.get(each)) : Through.NONE;
            if (through.isBroughtDownByHelpers()) {
                byHelpers.add(through);
            }
        }
        return new WhatToDeclare(conditions.size(), toDeclare(byHelpers),
                conditions.size() - byHelpers.size());
    }

    /** The helpers that leave every one of {@code conditions} with no more readings than are
     *  made, none of which can be left out. */
    private static List<HelperToDeclare> toDeclare(List<Through> conditions) {
        Map<ValueName.Helper, List<Held>> heldIn = new LinkedHashMap<>();
        conditions.forEach(each -> each.byHelper().forEach((helper, held) ->
                heldIn.computeIfAbsent(helper, _ -> new ArrayList<>()).add(held)));
        Set<ValueName.Helper> declared = new LinkedHashSet<>(heldIn.keySet());
        heldIn.entrySet().stream().sorted(Map.Entry.comparingByValue(
                Comparator.<List<Held>>comparingInt(List::size).thenComparing(inEach ->
                        inEach.stream().reduce(Held::and).orElseThrow().readings())))
                .forEach(each -> {
                    declared.remove(each.getKey());
                    if (conditions.stream().anyMatch(condition ->
                            condition.readingsWhere(declared).compareTo(left()) > 0)) {
                        declared.add(each.getKey());
                    }
                });
        return heldIn.entrySet().stream().filter(each -> declared.contains(each.getKey()))
                .map(each -> toDeclare(each.getKey(), each.getValue()))
                .sorted(Comparator.comparingInt(HelperToDeclare::conditions).reversed()).toList();
    }

    private static HelperToDeclare toDeclare(ValueName.Helper helper, List<Held> inEach) {
        Set<ExpansionLineage.Expansion> calls =
                inEach.stream().reduce(Held::and).orElseThrow().calls();
        return new HelperToDeclare(helper, inEach.size(), calls.size(), calls.stream()
                .flatMap(call -> CaseExpansion.helpersAround(call).stream()).distinct().toList());
    }

    /** The most readings {@code through} may come to. */
    static BigInteger readings(Collection<AChoiceReadThrough> through) {
        BigInteger out = BigInteger.ONE;
        for (AChoiceReadThrough each : through) {
            out = out.multiply(BigInteger.valueOf(each.readings()));
        }
        return out;
    }

    /** The choices of one condition that are written in the calls of one helper: the readings
     *  they come to, and the calls. */
    private record Held(BigInteger readings, Set<ExpansionLineage.Expansion> calls) {

        Held and(Held other) {
            Set<ExpansionLineage.Expansion> both = new LinkedHashSet<>(calls);
            both.addAll(other.calls);
            return new Held(readings.multiply(other.readings), both);
        }
    }

    /**
     * The choices one condition is read through, by what takes them out.
     *
     * @param beside   the readings the choices written beside the condition come to
     * @param byHelper for each helper declared, what is taken out
     */
    private record Through(BigInteger beside, Map<ValueName.Helper, Held> byHelper) {

        static final Through NONE = new Through(BigInteger.ONE, Map.of());

        static Through of(AComparisonRead condition) {
            BigInteger beside = BigInteger.ONE;
            Map<ValueName.Helper, Held> byHelper = new LinkedHashMap<>();
            for (AChoiceReadThrough choice : condition.through()) {
                BigInteger readings = BigInteger.valueOf(choice.readings());
                Optional<ExpansionLineage.Expansion> call =
                        copyCalled(condition.copy(), choice.construct());
                if (call.isEmpty()) {
                    beside = beside.multiply(readings);
                } else {
                    byHelper.merge((ValueName.Helper) call.get().expanded(),
                            new Held(readings, Set.of(call.get())), Held::and);
                }
            }
            return new Through(beside, byHelper);
        }

        /** Whether the choices come to more readings than are made, and do not where every
         *  helper they are written in is a behavior. */
        boolean isBroughtDownByHelpers() {
            return readingsWhere(Set.of()).compareTo(left()) > 0 && beside.compareTo(left()) <= 0;
        }

        /** The readings left where {@code declared} are behaviors. */
        BigInteger readingsWhere(Set<ValueName.Helper> declared) {
            BigInteger out = beside;
            for (Map.Entry<ValueName.Helper, Held> each : byHelper.entrySet()) {
                if (!declared.contains(each.getKey())) {
                    out = out.multiply(each.getValue().readings());
                }
            }
            return out;
        }
    }

    /**
     * The copy of a helper's body {@code choice} stands in that was made by a call written in a
     * body {@code condition} stands in as well: the outermost copy around the choice that is not
     * around the condition. That call is the one that becomes a call of a behavior; none where
     * the choice is written beside the condition.
     */
    private static Optional<ExpansionLineage.Expansion> copyCalled(ModelOccurrence condition,
                                                                  ModelOccurrence choice) {
        Set<ExpansionLineage> around = new LinkedHashSet<>();
        for (ExpansionLineage each = condition.lineage();
                each instanceof ExpansionLineage.Expansion step; each = step.within()) {
            around.add(step);
        }
        ExpansionLineage.Expansion outermost = null;
        for (ExpansionLineage each = choice.lineage();
                each instanceof ExpansionLineage.Expansion step; each = step.within()) {
            if (around.contains(step)) {
                break;
            }
            if (step.expanded() instanceof ValueName.Helper) {
                outermost = step;
            }
        }
        return Optional.ofNullable(outermost);
    }
}
