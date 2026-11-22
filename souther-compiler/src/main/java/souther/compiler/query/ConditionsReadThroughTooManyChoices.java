package souther.compiler.query;

import souther.compiler.meaning.CaseExpansion;
import souther.compiler.partition.AChoiceReadThrough;
import souther.compiler.partition.AComparisonRead;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * The conditions of one behavior whose values are made through more choices than this compiler
 * reads one condition on, and the helpers to declare as behaviors so that they are not.
 *
 * <p><b>Asked of how the values are written, before anything is read of the conditions.</b> A
 * condition is read once on each arm of a choice its values are made through, and what decides
 * between the arms is read beside them, so the readings multiply with each choice
 * ({@link AChoiceReadThrough#readings}). What is counted here is the most they may come to: an arm
 * no run takes is not read, so a condition told of here may be read whole all the same. Told of
 * before the reading, it is what the reading may cost; where the reading stopped at the figure, it
 * is why.
 *
 * <p><b>And what to do is what takes the choices out.</b> What a behavior answers is one value to
 * whoever calls it, so a helper declared as one leaves none of the choices written in it, or in
 * what it calls, for the condition to be read through. The helpers named are the fewest found, the
 * one that takes out most first, whose choices taken out leave no more readings than
 * {@link CompositionBudget#READINGS_OF_ONE_CONDITION} allows; and where the choices written beside
 * the condition come to more than that by themselves, the condition is told of as one that is.
 *
 * @param name     the module
 * @param behavior the behavior
 */
public record ConditionsReadThroughTooManyChoices(String name, String behavior)
        implements Key<ConditionsReadThroughTooManyChoices.Told> {

    /** The readings of one condition past which it is told of. */
    public static int most() {
        return CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.maximum();
    }

    /** The readings a condition is left with where the helpers named are behaviors. */
    private static int left() {
        return CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
    }

    /** What is told of one behavior of one module. */
    public record Said(String module, String behavior, Told told) {}

    /**
     * What is told of each behavior {@code compilation} measures, in the order they are declared,
     * leaving out those nothing is told of. Nothing the measurement makes is asked for it.
     */
    public static List<Said> toldOf(Compilation compilation) {
        List<Said> out = new ArrayList<>();
        WhatIsBeingMeasured.toBeMeasuredIn(compilation).forEach((module, behaviors) ->
                behaviors.forEach(behavior -> {
                    Told told = compilation.db()
                            .ask(new ConditionsReadThroughTooManyChoices(module, behavior))
                            .value();
                    if (told != null && told.conditions() > 0) {
                        out.add(new Said(module, behavior, told));
                    }
                }));
        return List.copyOf(out);
    }

    /**
     * What is told of one behavior.
     *
     * @param conditions how many conditions are told of
     * @param helpers    the helpers to declare as behaviors, the one taking out the choices of the
     *                   most conditions first
     * @param beside     how many of the conditions are past the readings by the choices written
     *                   beside them, whatever helper is declared
     */
    public record Told(int conditions, List<HelperToDeclare> helpers, int beside) {

        /** Nothing is told of. */
        public static final Told NOTHING = new Told(0, List.of(), 0);

        public Told {
            helpers = List.copyOf(helpers);
        }
    }

    /**
     * A helper to declare as a behavior.
     *
     * @param helper       the helper
     * @param conditions   how many conditions its choices are taken out of
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

    @Override
    public String module() {
        return name;
    }

    @Override
    public Answer<Told> compute(Db db) {
        List<AComparisonRead> read = db.ask(new Adequacy.ComparisonsRead(name, behavior)).value();
        return read == null ? Answer.absent() : Answer.of(told(read));
    }

    /** What is told of {@code conditions}, each where the walk of the body met it. */
    static Told told(List<AComparisonRead> conditions) {
        Map<ValueName.Helper, Gathered> byHelper = new LinkedHashMap<>();
        int past = 0;
        int beside = 0;
        for (AComparisonRead each : conditions) {
            if (readings(each.through()) <= most()) {
                continue;
            }
            past++;
            List<AChoiceReadThrough> through = new ArrayList<>(each.through());
            while (readings(through) > left()) {
                Optional<ValueName.Helper> most = takingOutMost(each.copy(), through);
                if (most.isEmpty()) {
                    beside++;
                    break;
                }
                ValueName.Helper helper = most.get();
                Gathered gathered = byHelper.computeIfAbsent(helper, _ -> new Gathered());
                gathered.conditions++;
                through.removeIf(choice -> copyCalled(each.copy(), choice.construct())
                        .filter(copy -> copy.expanded().equals(helper))
                        .map(copy -> {
                            gathered.calls.add(copy);
                            return true;
                        }).orElse(false));
            }
        }
        List<HelperToDeclare> helpers = new ArrayList<>();
        byHelper.forEach((helper, gathered) -> helpers.add(gathered.of(helper)));
        helpers.sort((one, other) -> Integer.compare(other.conditions(), one.conditions()));
        return new Told(past, helpers, beside);
    }

    /** The most readings {@code through} may come to, no further than is past every figure. */
    private static long readings(Collection<AChoiceReadThrough> through) {
        long out = 1;
        for (AChoiceReadThrough each : through) {
            out *= each.readings();
            if (out > most()) {
                return out;
            }
        }
        return out;
    }

    /** The helper whose calls, as {@code condition} is read through them, hold the most of
     *  {@code choices}; none where no choice is inside such a call. */
    private static Optional<ValueName.Helper> takingOutMost(ModelOccurrence condition,
                                                            List<AChoiceReadThrough> choices) {
        Map<ValueName.Helper, Integer> held = new LinkedHashMap<>();
        for (AChoiceReadThrough each : choices) {
            copyCalled(condition, each.construct()).ifPresent(copy ->
                    held.merge((ValueName.Helper) copy.expanded(), 1, Integer::sum));
        }
        ValueName.Helper most = null;
        for (Map.Entry<ValueName.Helper, Integer> each : held.entrySet()) {
            if (most == null || each.getValue() > held.get(most)) {
                most = each.getKey();
            }
        }
        return Optional.ofNullable(most);
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

    /** The conditions one helper's choices are taken out of, gathered. */
    private static final class Gathered {

        private final Set<ExpansionLineage.Expansion> calls = new LinkedHashSet<>();
        private int conditions;

        HelperToDeclare of(ValueName.Helper helper) {
            List<ValueName.Helper> inside = calls.stream()
                    .flatMap(call -> CaseExpansion.helpersAround(call).stream())
                    .distinct().collect(Collectors.toList());
            return new HelperToDeclare(helper, conditions, calls.size(), inside);
        }
    }
}
