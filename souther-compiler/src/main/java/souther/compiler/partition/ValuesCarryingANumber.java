package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.SequencedMap;

/**
 * The values of a plan where one position inside it holds a number the caller has, and others hold
 * values the caller fixed beside it.
 *
 * <p>What a walk filling a container to a total needs: each element is a whole value of its own
 * type with the number at the path the total reads, whatever else the caller asked the element to
 * hold at the positions it named, and everything beside those chosen the way any value of that type
 * is.
 *
 * <p>A source of values and not a second reading of the plan. Which positions are under a position,
 * which case a value is narrowed to, what a container holds and which names a value still has to
 * wear are {@link ConstructionPlan}'s answers, read by {@link PlanComposer} for every caller —
 * walked here from the declarations instead, this agreed wherever the way down was records and lost
 * the value at every sum, newtype and container.
 *
 * <p>So what is left here is one question: where a record's fields come from. The ones a value the
 * caller has is under come from below, and the rest are chosen against the record's own rules, read
 * again once those values are in them — so what is offered is a value the model may well admit
 * rather than a shape that carries the number and breaks a rule about the field next to it.
 *
 * @param fixed    the position the number is written at, which is one the plan was made against
 * @param value    the number, as the position's own carrier writes it
 * @param beside   the values the caller fixed at other positions the plan was made against, each
 *                 already a value of its position
 * @param narrowed the positions the caller said which case of, which the plan was made against
 *                 too — what stands there is the plan's to build, and a field filled from its
 *                 declaration alone would be whichever case that walk came to first
 */
record ValuesCarryingANumber(TermPath fixed, FixtureTemplate value,
                             Map<TermPath, FixtureTemplate> beside, Set<TermPath> narrowed,
                             RuleReadingContext reading)
        implements PlanComposer.Values {

    ValuesCarryingANumber {
        beside = Map.copyOf(beside);
        narrowed = Set.copyOf(narrowed);
    }

    @Override
    public FixtureTemplate at(ConstructionPlan.Slot slot) {
        // A value the caller fixed is a value of its position already, and stands as it is.
        FixtureTemplate given = beside.get(slot.at());
        if (given != null) {
            return given;
        }
        // The value itself, under every name the position wears. What the caller hands over is a
        // number and not a value of the position, so the names its own type wears go on here — the
        // plan's `worn` is what a value already wearing those is still missing, which is what a
        // value chosen at a slot by a search is.
        return slot.at().equals(fixed)
                ? WornNames.under(TypeView.of(slot.type(), reading.source().inners(),
                                reading.source().symbols(),
                                reading.source().kinds(),
                                reading.source().sums()).wrappers(),
                        value, reading.source())
                : null;
    }

    @Override
    public SequencedMap<String, FixtureTemplate> under(ConstructionPlan.Built built,
                                                       PlanComposer.Under under) {
        // A constructor this cannot name is a value nothing here writes, which is what the empty
        // answer says.
        if (!(built.of() instanceof TypeSymbol.AtModule record)) {
            return null;
        }
        Map<String, FixtureTemplate> composed = new LinkedHashMap<>();
        for (Map.Entry<String, ConstructionPlan.Node> each : built.under().entrySet()) {
            if (!holdsSomethingAsked(each.getValue())) {
                continue;
            }
            FixtureTemplate inner = under.of(each.getValue());
            if (inner == null) {
                return null;
            }
            composed.put(each.getKey(), inner);
        }
        if (composed.isEmpty()) {
            return null;
        }
        return Partitions.fieldsOf(record, reading, Set.of(), composed);
    }

    /**
     * Whether something the caller has is at or under {@code node}.
     *
     * <p>Asked of the plan's own positions rather than of the paths' steps. The two agree wherever
     * a field step is a field of a record, and part where a narrowing takes no level: the plan's
     * position for a case is written at the same remove as the sum it narrows, so a walk counting
     * steps would be one out from there down.
     */
    private boolean holdsSomethingAsked(ConstructionPlan.Node node) {
        if (fixed.isAtOrUnder(node.at())) {
            return true;
        }
        for (TermPath each : beside.keySet()) {
            if (each.isAtOrUnder(node.at())) {
                return true;
            }
        }
        for (TermPath each : narrowed) {
            if (each.isAtOrUnder(node.at())) {
                return true;
            }
        }
        return false;
    }
}
