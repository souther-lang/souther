package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * The value a construction plan builds.
 *
 * <p>What a plan means as a value is decided here and nowhere else: which positions are under a
 * position, what a container holds, what a narrowing settled, and which names a value still has to
 * wear. Two readers had this walk each — the search, composing what its assignment chose, and the
 * walk that puts a number inside a value — and what they differed in was never the plan.
 *
 * <p><b>What differs is where a record's fields come from.</b> A search has values for all of them
 * and hands them over; a walk with one position fixed has that one and chooses the rest against the
 * record's own rules. That is two questions about values and one answer about the plan, so it is the
 * one thing a caller brings ({@link Values}).
 */
final class PlanComposer {

    /**
     * Where the values in a plan's positions come from.
     *
     * <p>Both halves are about values and neither is about the plan. A caller that answered
     * anything else here — which positions are under this one, what a container holds — would be
     * reading the plan a second time.
     */
    interface Values {

        /** What stands at a position the plan chooses a whole value at, or null where nothing does. */
        FixtureTemplate at(ConstructionPlan.Slot slot);

        /**
         * What stands at each field of a record the plan composes, or null where one of them has
         * nothing to stand for it.
         *
         * @param under composes a position of the plan, which is how a caller reaches the fields it
         *              does have a value under. Handed over rather than left to the caller so that
         *              what is below a field is still read the one way
         */
        Map<String, FixtureTemplate> under(ConstructionPlan.Built built, Under under);
    }

    /** Composing one position of the plan, which is what a caller is given to reach below a field. */
    interface Under {

        /** The value at {@code node}, or null where nothing here builds one. */
        FixtureTemplate of(ConstructionPlan.Node node);
    }

    /**
     * The value at one position of the plan, or null where nothing builds one.
     *
     * <p>Null travels up: a field with nothing at it is a record with nothing at it, because what
     * would be written instead is a value of a type the position does not declare.
     */
    static FixtureTemplate compose(ConstructionPlan.Node node, Values values,
                                   RuleReadingSource ruleSource, ReadingPolicy policy) {
        return switch (node) {
            // Under the names the position wore before a narrowing reached it, and under none where
            // none did: what stands at a slot is a value of the narrowed type, already written
            // under whatever names that type wears, and a `data DecisionN = Decision` narrowed to
            // one of its cases is written `DecisionN(...)` all the same.
            case ConstructionPlan.Slot slot -> worn(slot.worn(), values.at(slot), ruleSource);
            case ConstructionPlan.Built built -> composed(built, values, ruleSource, policy);
            case ConstructionPlan.Held held -> held(held, values, ruleSource, policy);
            // The requirement settled this one, so nothing was chosen for it and there is nothing to
            // look up. Under every name the position wears, since the value arrives bare.
            case ConstructionPlan.Exact exact -> worn(exact.worn(), exact.exact(), ruleSource);
        };
    }

    /**
     * {@code value} under {@code worn}, or {@code value} where nothing is worn over it.
     *
     * <p>Null where a name the position wears is one this module cannot write, which is a value
     * that cannot be written rather than one written without the name.
     */
    static FixtureTemplate worn(List<TypeOps.Layer> worn, FixtureTemplate value,
                                RuleReadingSource ruleSource) {
        if (value == null || worn.isEmpty()) {
            return value;
        }
        List<TypeReachName.Written> names = written(worn, ruleSource);
        return names == null ? null : RepresentativeSource.under(names, value);
    }

    /**
     * The names a position wears as this module writes them, or null where one of them is a name it
     * cannot write.
     *
     * <p>Null takes the whole value with it: the name goes on the value as it is written, and a
     * value composed without one is of a type the parameter does not declare. Asked in one place
     * because every value this composes needs the same answer, and three copies of the loop are
     * three chances to differ about what a name this module cannot reach comes to.
     */
    private static List<TypeReachName.Written> written(List<TypeOps.Layer> worn,
                                                       RuleReadingSource ruleSource) {
        List<TypeReachName.Written> names = new ArrayList<>();
        for (TypeOps.Layer layer : worn) {
            if (!(ruleSource.symbols().scope().reach(layer.named())
                    instanceof TypeReachName.Written name)) {
                return null;
            }
            names.add(name);
        }
        return names;
    }

    /**
     * The list of one this plan builds around what stands at its element.
     *
     * <p>Under the names the position is written with, as a record is: a row at a
     * {@code data Basket = List<Item>} carries {@code Basket([...])}, and a list composed without
     * them is of a type the parameter does not declare.
     */
    private static FixtureTemplate held(ConstructionPlan.Held plan, Values values,
                                        RuleReadingSource ruleSource, ReadingPolicy policy) {
        FixtureTemplate element = compose(plan.under(), values, ruleSource, policy);
        if (element == null) {
            return null;
        }
        // The one placed in the class, and enough beside it for the collection to be one the rules
        // admit. What may stand beside it is the carrier's business — a list may hold the same
        // value again and a set may not — so the collection is asked for whole rather than padded
        // here.
        if (!(TypeView.of(plan.type(), ruleSource.symbols()).shape()
                instanceof Shape.Sequence carrier)) {
            return null;
        }
        FixtureTemplate collection =
                Witnesses.holdingAlso(carrier, element, plan.least(), ruleSource, policy);
        if (collection == null) {
            return null;
        }
        // A name this module cannot write leaves no value to write.
        List<TypeReachName.Written> worn = written(plan.worn(), ruleSource);
        return worn == null ? null : RepresentativeSource.under(worn, collection);
    }

    /** One record of the plan, out of whatever the caller has at the positions under it. */
    private static FixtureTemplate composed(ConstructionPlan.Built built, Values values,
                                            RuleReadingSource ruleSource, ReadingPolicy policy) {
        Map<String, FixtureTemplate> fields =
                values.under(built, node -> compose(node, values, ruleSource, policy));
        if (fields == null) {
            return null;
        }
        // Under the names the position is written with, which the descent that found the fields took
        // off to find them. A row at a `data SlotN = Slot` carries `SlotN(Slot { ... })`, and a value
        // composed without them is of a type the parameter does not declare.
        // A name this module cannot write leaves no value to write.
        List<TypeReachName.Written> worn = written(built.worn(), ruleSource);
        if (worn == null
                || !(ruleSource.symbols().scope().reach(built.of())
                        instanceof TypeReachName.Written written)) {
            return null;
        }
        // Under every name the position wears, which where a refinement narrowed it are the names
        // it wore before the narrowing and the ones the narrowed value wears after it. One list and
        // one putting-back-on: read as two, the outer names had to be recovered from the class that
        // asked for the narrowing rather than from the position they belong to.
        return RepresentativeSource.under(worn, FixtureTemplate.record(written, fields));
    }

    private PlanComposer() {}
}
