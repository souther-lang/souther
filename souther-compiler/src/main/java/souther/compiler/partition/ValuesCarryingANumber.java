package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Map;

/**
 * Values built with a number written somewhere inside them.
 *
 * <p>What a walk filling a container to a total asks for: each element is a whole value of its own
 * type with the number at the path the total reads, and everything beside it is chosen the way any
 * value of that type is.
 *
 * <p><b>The way down is the plan's and none of this reader's.</b> Which positions are under a
 * position, which case a value is narrowed to, what a container holds and which names a value still
 * has to wear are {@link ConstructionPlan}'s answers. Walked here from the declarations instead,
 * this was a second reading of them: it agreed wherever a field is a field of a plain record and
 * lost the value at every sum, newtype and container, and each of those came back as one silence.
 *
 * <p>So what is left here is the filling. A record is composed by the reader that has its rules, and
 * the names a position wears go on where the plan says they do.
 *
 * <p><b>One occurrence of the number per element.</b> The walk that asks for this splits a total
 * over the elements of one container, so a container between an element and the number is a value
 * whose occurrences are not the ones that were split. Nothing is composed there rather than a value
 * coming to a multiple of what was asked for.
 */
final class ValuesCarryingANumber {

    /**
     * The value the plan builds at {@code node}, holding {@code value} at {@code fixed}, or null
     * where nothing here builds one.
     *
     * <p>The value at the position is the caller's and everything beside it is chosen against the
     * rules of the record it sits in, read again once the caller's value is in them — so what is
     * offered is a value the model may well admit rather than a shape that carries the number and
     * breaks a rule about the field next to it.
     */
    static FixtureTemplate carrying(ConstructionPlan.Node node, TermPath fixed, FixtureTemplate value,
                                    RuleReadingSource ruleSource, ReadingPolicy policy) {
        if (value == null || !fixed.isAtOrUnder(node.at())) {
            return null;
        }
        return switch (node) {
            // The value itself, under every name the position wears. Both halves: what the caller
            // hands over is a number and not a value of the position, so the names its own type
            // wears go on here — the plan's `worn` is what a value that already wears those is
            // still missing, which is what a value chosen at a slot by the search is.
            case ConstructionPlan.Slot slot -> slot.at().equals(fixed)
                    ? Generator.worn(slot.worn(),
                            Witnesses.wrapped(slot.type(), value, ruleSource), ruleSource)
                    : null;
            // A narrowing settled the value here, so there is no position under it for anything to
            // be written at. Nothing reaches this — the plan refuses a demand under a position it
            // settles — and it is answered rather than assumed away.
            case ConstructionPlan.Exact _ -> null;
            case ConstructionPlan.Built built -> {
                Map.Entry<String, ConstructionPlan.Node> down = fieldTowards(built, fixed);
                FixtureTemplate inner = down == null ? null
                        : carrying(down.getValue(), fixed, value, ruleSource, policy);
                // A record this module composes is one a module declares. A constructor this cannot
                // name is a value nothing here writes, which is what the empty answer below says.
                if (inner == null || !(built.of() instanceof TypeSymbol.AtModule record)) {
                    yield null;
                }
                // The rest of the record is chosen against what its own rules leave each field,
                // which is the reading `Partitions.composed` makes of them. Chosen from the types
                // alone, a record whose rule relates two fields would be handed a value it refuses.
                List<FixtureTemplate> whole = Partitions.composed(record, ruleSource, policy,
                        java.util.Set.of(), Map.of(down.getKey(), inner));
                yield whole.isEmpty() ? null
                        : Generator.worn(built.worn(), whole.getFirst(), ruleSource);
            }
            // A container between the element and the number, which is more occurrences of the
            // number than the walk that split the total counted. The split is one number per
            // element of the outer container, and a container here holds as many as its own rules
            // ask for -- so a value built here would come to a multiple of the total it was built
            // for. Nothing composes one until what is decomposed is the occurrences rather than the
            // elements, and that is a question for the walk that decomposes.
            case ConstructionPlan.Held _ -> null;
        };
    }

    /**
     * The field of {@code built} the fixed position is at or under, or null where none is.
     *
     * <p>Asked of the plan's own positions rather than of the path's steps. The two agree wherever
     * a field step is a field of a record, and part where a narrowing takes no level: the plan's
     * position for a case is written at the same remove as the sum it narrows, so a walk counting
     * steps would be one out from there down.
     */
    private static Map.Entry<String, ConstructionPlan.Node> fieldTowards(ConstructionPlan.Built built,
                                                                        TermPath fixed) {
        for (Map.Entry<String, ConstructionPlan.Node> each : built.under().entrySet()) {
            if (fixed.isAtOrUnder(each.getValue().at())) {
                return each;
            }
        }
        return null;
    }

    private ValuesCarryingANumber() {}
}
