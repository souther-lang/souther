package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.List;

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

        /** What stands at a position the plan chooses a whole value at, or nothing where nothing
         *  does — with what building it met. */
        Proposals at(ConstructionPlan.Slot slot);

        /**
         * What stands at each field of a record the plan composes, or none where one of them has
         * nothing to stand for it — with what choosing them met.
         *
         * @param under composes a position of the plan, which is how a caller reaches the fields it
         *              does have a value under. Handed over rather than left to the caller so that
         *              what is below a field is still read the one way
         *
         *              <p>Answered in the order the record declares its fields, and answered as
         *              something that has one, because a fixture is written field by field in that
         *              order and a caller handed only which fields there are would write them in
         *              whatever a walk of them came to.
         */
        Partitions.FieldsChosen under(ConstructionPlan.Built built, Under under);

        /**
         * What the container at {@code container} is to hold and to hold nothing equal to, or null
         * where a value it is handed has nothing to stand for it.
         *
         * <p>Asked only of a container the plan says values are handed to
         * ({@link ConstructionPlan.Held#handed}), so a caller that hands none over has nothing to
         * answer and is never asked.
         *
         * @param under composes a position of the plan, which is how a value read at a position of
         *              the same value is reached — composed the one way every position is
         */
        ContainerContents contentsOf(TermPath container, Under under);
    }

    /** Composing one position of the plan, which is what a caller is given to reach below a field. */
    interface Under {

        /** The value at {@code node}, or nothing where nothing here builds one, with what
         *  building it met. */
        Proposals of(ConstructionPlan.Node node);
    }

    /**
     * The value at one position of the plan, or nothing where nothing builds one — with what of
     * this compiler's building it met.
     *
     * <p>Nothing travels up: a field with nothing at it is a record with nothing at it, because what
     * would be written instead is a value of a type the position does not declare. And what was
     * met travels up with it, so a record with nothing because a container in it is past a figure
     * is not read as a record the decoder refused.
     */
    static Proposals compose(ConstructionPlan.Node node, Values values,
                             RuleReadingContext reading) {
        RuleReadingSource ruleSource = reading.source();
        return switch (node) {
            // Under the names the position wore before a narrowing reached it, and under none where
            // none did: what stands at a slot is a value of the narrowed type, already written
            // under whatever names that type wears, and a `data DecisionN = Decision` narrowed to
            // one of its cases is written `DecisionN(...)` all the same.
            case ConstructionPlan.Slot slot -> {
                Proposals at = values.at(slot);
                yield new Proposals(at.isEmpty() ? List.of() : one(WornNames.under(slot.worn(),
                        at.values().getFirst(), ruleSource)), at.met());
            }
            case ConstructionPlan.Built built -> composed(built, values, reading);
            case ConstructionPlan.Held held -> held(held, values, reading);
            // The requirement settled this one, so nothing was chosen for it and there is nothing to
            // look up. Under every name the position wears, since the value arrives bare.
            case ConstructionPlan.Exact exact ->
                    Proposals.of(one(WornNames.under(exact.worn(), exact.exact(), ruleSource)));
        };
    }

    /** {@code value} alone, or none where there is none. */
    private static List<FixtureTemplate> one(FixtureTemplate value) {
        return value == null ? List.of() : List.of(value);
    }

    /** What composing the positions a container is handed values from met. */
    private static final class Met {

        private CompositionShortfall met = CompositionShortfall.NONE;

        Proposals noting(Proposals composed) {
            met = met.and(composed.met());
            return composed;
        }
    }

    /**
     * The collection this plan builds around what it is asked to hold.
     *
     * <p>What stands at its element where a class is put there, the values the caller hands over,
     * and as many beside them as the rules ask for: what a class at an element asks for is a
     * collection holding a value in it, and where the rules ask the collection for more than that
     * a collection of one is not a row.
     *
     * <p>Under the names the position is written with, as a record is: a row at a
     * {@code data Basket = List<Item>} carries {@code Basket([...])}, and a list composed without
     * them is of a type the parameter does not declare.
     */
    private static Proposals held(ConstructionPlan.Held plan, Values values,
                                  RuleReadingContext reading) {
        List<FixtureTemplate> holding = new ArrayList<>();
        List<FixtureTemplate> keptOut = List.of();
        List<FixtureTemplate> keysHeld = List.of();
        List<FixtureTemplate> keysEachFiled = List.of();
        List<FixtureTemplate> keysKeptOut = List.of();
        CompositionShortfall met = CompositionShortfall.NONE;
        FixtureTemplate element = null;
        if (plan.composesItsElement()) {
            Proposals composed = compose(plan.under().get(), values, reading);
            met = composed.met();
            if (composed.isEmpty()) {
                return new Proposals(List.of(), met);
            }
            element = composed.values().getFirst();
            holding.add(element);
        }
        if (plan.handed()) {
            Met handed = new Met();
            ContainerContents contents = values.contentsOf(plan.at(),
                    node -> handed.noting(compose(node, values, reading)));
            met = met.and(handed.met);
            if (contents == null) {
                return new Proposals(List.of(), met);
            }
            holding.addAll(contents.holding());
            keptOut = contents.keptOut();
            keysHeld = contents.keysHeld();
            keysEachFiled = contents.keysEachFiled();
            keysKeptOut = contents.keysKeptOut();
        }
        RuleReadingSource ruleSource = reading.source();
        // What may stand beside them is the carrier's business — a list may hold the same value
        // again and a set may not, and a map's values stand under keys of their own — so the
        // collection is asked for whole rather than padded here.
        if (!(TypeView.shapeOf(plan.type(), ruleSource.inners(), ruleSource.symbols(),
                ruleSource.kinds(), ruleSource.sums())
                instanceof Shape.Container container)) {
            return new Proposals(List.of(), met);
        }
        // The key the plan put the element under, or over whatever value the rules admit where
        // nothing was asked of the value.
        FixtureTemplate key = null;
        if (plan.key().isPresent()) {
            Proposals composed = compose(plan.key().get(), values, reading);
            met = met.and(composed.met());
            if (composed.isEmpty()) {
                return new Proposals(List.of(), met);
            }
            key = composed.values().getFirst();
        }
        // A key the rules ask the entry to be filed under is a value of another position, and one
        // entry is filed under one key.
        for (FixtureTemplate asked : keysHeld) {
            if (key != null && !key.text().equals(asked.text())) {
                return new Proposals(List.of(), met);
            }
            key = asked;
        }
        Proposals collection = switch (container) {
            case Shape.Sequence carrier -> {
                // Every element is the one composed, and elements kept apart — a set's, or a
                // list's its rules or those of what holds it keep apart — hold it once: one the
                // rules ask to hold more has no room for them all to be it.
                List<List<String>> apart =
                        ElementsKeptApart.at(plan.worn(), carrier, plan.keptApart(), reading);
                if (plan.eachOf() && !apart.isEmpty() && plan.holds().least() > 1) {
                    yield Proposals.NONE;
                }
                if (key != null || !keysEachFiled.isEmpty()) {
                    throw new IllegalStateException("a plan put a key on what a list or a set"
                            + " holds, which files nothing under one: " + plan.at());
                }
                yield Witnesses.holding(carrier, apart, holding, keptOut, plan.holds(), reading);
            }
            case Shape.Mapping carrier -> Witnesses.holding(carrier, holding, keptOut,
                    key == null ? null : new Witnesses.Filed(key, element), keysEachFiled,
                    keysKeptOut, plan.holds(), reading);
        };
        met = met.and(collection.met());
        // A name this module cannot write leaves no value to write.
        return new Proposals(collection.isEmpty() ? List.of()
                : one(WornNames.under(plan.worn(), collection.values().getFirst(), ruleSource)),
                met);
    }

    /** One record of the plan, out of whatever the caller has at the positions under it. */
    private static Proposals composed(ConstructionPlan.Built built, Values values,
                                      RuleReadingContext reading) {
        Partitions.FieldsChosen chosen =
                values.under(built, node -> compose(node, values, reading));
        if (chosen.fields() == null) {
            return new Proposals(List.of(), chosen.met());
        }
        RuleReadingSource ruleSource = reading.source();
        // Under the names the position is written with, which the descent that found the fields took
        // off to find them. A row at a `data SlotN = Slot` carries `SlotN(Slot { ... })`, and a value
        // composed without them is of a type the parameter does not declare.
        // A name this module cannot write leaves no value to write.
        if (!(ruleSource.symbols().scope().reach(built.of())
                instanceof TypeReachName.Written written)) {
            return new Proposals(List.of(), chosen.met());
        }
        // Under every name the position wears, which where a refinement narrowed it are the names
        // it wore before the narrowing and the ones the narrowed value wears after it. One list and
        // one putting-back-on: read as two, the outer names had to be recovered from the class that
        // asked for the narrowing rather than from the position they belong to.
        return new Proposals(one(WornNames.under(built.worn(),
                FixtureTemplate.record(written, chosen.fields()), ruleSource)), chosen.met());
    }

    private PlanComposer() {}
}
