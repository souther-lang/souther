package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.Prepared;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value handed to another parameter's container from inside some element is planned inside that
 * element, and a value read off every element is not made to stand.
 *
 * <p>The two are the same position read for two statements. Some element of {@code items} filed in
 * {@code shelf} is met only by a row whose list holds one, so the element is a position of the plan
 * and the list holds it — and where the rules keep the list empty, that is the model's answer.
 * Every element of {@code items} filed in {@code shelf} is met by a list holding none as well, so
 * the value read is no reason for the list to hold anything, and the rules keeping it empty refuse
 * nothing.
 *
 * <p>What a plan for the second comes to beyond that is not held here: it is not composed yet, and
 * what it is not is all this pins.
 */
class AValueHandedOnFromSomeElementIsPlannedInsideThatElementTest {

    private static final ConstructionPlan.WhatItMayHold ANY = (_, _) ->
            ConstructionPlan.ItMayHold.counting(new DeclaredBounds.CountRange(0, Integer.MAX_VALUE));

    private static final ConstructionPlan.WhatItMayHold NONE_OF_THEM =
            (_, _) -> ConstructionPlan.ItMayHold.counting(new DeclaredBounds.CountRange(0, 0));

    private static final String MODEL = """
            module g

            data Item = { sku: String, q: Int }

            behavior pick : (items: List<Item>, filed: Map<String, Item>) -> Int
            """;

    private static final TermPath ITEMS = TermPath.of("items");
    private static final TermPath FILED = TermPath.of("filed");
    private static final TermPath SHELF = TermPath.of("shelf");
    private static final TermPath SKU = ITEMS.element().then("sku");

    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt("g",
                    new ConditionOccurrence("pick", ConditionOccurrence.Reading.DIVIDING, 0));

    /** What the container holding one or none is said as, which nothing here reads. */
    private static final RowDemand.Relational HOLDING = new RowDemand.Relational(
            new TakenConstraint.Affine(
                    LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("n"))), Rel.GE));

    private static ContentsAsked asked(RowDemand.OfACondition demand) {
        return ContentsAsked.of(List.of(new OnTheWay.TakenIn(WHERE, demand)));
    }

    private static RowDemand.WithinIt keyedInTheShelf(TermPath value) {
        return new RowDemand.WithinIt(SHELF, true, new RowDemand.KeyedAs(value));
    }

    /** What the plan of {@code head} is to hold, where nothing composed before handed anything on. */
    private static ConstructionPlan.ContentsComposed composedUnder(ContentsAsked asked,
                                                                   String head) {
        ContentsAsked.Resolution resolution = asked.resolvedFor(head, ValuesHandedOn.NONE);
        ContentsAsked.Resolution.Resolved resolved = assertInstanceOf(
                ContentsAsked.Resolution.Resolved.class, resolution,
                () -> "nothing is handed to a container of `" + head + "`: " + resolution);
        return asked.composedUnder(head, resolved.here());
    }

    private static ConstructionPlan.ContentsComposed someItemFiled() {
        return composedUnder(
                asked(new RowDemand.Exists(ITEMS, only(keyedInTheShelf(SKU)), HOLDING,
                        Optional.empty())),
                "items");
    }

    private static ConstructionPlan.ContentsComposed everyItemFiled() {
        return composedUnder(
                asked(new RowDemand.ForAll(ITEMS, only(keyedInTheShelf(SKU)), HOLDING,
                        Optional.empty())),
                "items");
    }

    @Test
    void aValueReadOffSomeElementStands() {
        ConstructionPlan.ContentsComposed contents = someItemFiled();

        assertEquals(Set.of(SKU), contents.read());
        assertEquals(Set.of(SKU), contents.standing());
    }

    /**
     * Read off every element, the value is read off what was built, element by element, and is no
     * position of the plan: a list holding none meets the demand, and a position chosen inside it
     * would make it hold one.
     */
    @Test
    void aValueReadOffEveryElementIsNoPositionOfThePlan() {
        ConstructionPlan.ContentsComposed contents = everyItemFiled();

        assertEquals(Set.of(), contents.read());
        assertEquals(Set.of(), contents.standing());
    }

    /**
     * Some element of the outer list, and a list inside it nothing quantifies: the value is under
     * both, and only one of them is asked to hold an element.
     */
    @Test
    void aValueUnderAContainerNoDemandQuantifiesDoesNotStand() {
        TermPath deeper = ITEMS.element().then("tags").element();

        assertEquals(Set.of(), composedUnder(asked(new RowDemand.Exists(ITEMS,
                        only(keyedInTheShelf(deeper)), HOLDING, Optional.empty())), "items")
                .standing());
    }

    /**
     * Two quantifiers, one inside the other, and a value read under either container: it stands
     * where both containers it could be under hold an element in every row meeting the demand.
     *
     * <p>A quantifier inside one asking every element is reached only where that container holds
     * something, so some element of the inner one is no promise: a row holding none outside meets
     * the whole of it with the inner container empty. A quantifier asking every element inside one
     * asking some takes nothing from the outer one's element.
     */
    @Test
    void whetherAValueStandsFollowsEveryQuantifierAroundIt() {
        TermPath ofTheItem = ITEMS.element();
        TermPath ofTheShelf = SHELF.key();

        assertTrue(stands(true, true, ofTheItem), "some item, some entry: the item's value");
        assertTrue(stands(true, true, ofTheShelf), "some item, some entry: the entry's key");
        assertFalse(stands(false, true, ofTheShelf),
                "every item, some entry: no item, and no entry asked for");
        assertTrue(stands(true, false, ofTheItem), "some item, every entry: the item's value");
        assertFalse(stands(true, false, ofTheShelf), "some item, every entry: a shelf of none");
    }

    /**
     * Whether {@code value} stands, read off {@code items} asked {@code someItem} and inside it
     * {@code shelf} asked {@code someEntry} — holding the value as a key, or holding none equal to
     * it.
     */
    private static boolean stands(boolean someItem, boolean someEntry, TermPath value) {
        RowDemand.WithinIt inside = new RowDemand.WithinIt(SHELF, someEntry, someEntry
                ? new RowDemand.KeyedAs(value) : new RowDemand.NotKeyedAs(value));
        ContentsAsked asked = asked(someItem
                ? new RowDemand.Exists(ITEMS, only(inside), HOLDING, Optional.empty())
                : new RowDemand.ForAll(ITEMS, only(inside), HOLDING, Optional.empty()));
        ContentsAsked.Asked one = asked.asked().getFirst();
        assertEquals(value, one.value(), () -> "the one thing asked: " + asked);
        return one.standsWhereMet();
    }

    @Test
    void theElementAValueStandsInIsPlannedAndTheValueInsideIt() {
        ConstructionPlan plan = planned(0, someItemFiled(), ANY);

        ConstructionPlan.Held held = assertInstanceOf(ConstructionPlan.Held.class,
                plan.at(ITEMS), "the list is built around what it holds");
        ConstructionPlan.Built element = assertInstanceOf(ConstructionPlan.Built.class,
                held.under().orElseThrow(), () -> "its element is built: " + held);
        assertTrue(element.under().containsKey("sku"),
                () -> "and the value handed on is a position of it: " + element);
    }

    @Test
    void aListTheRulesKeepEmptyIsRefusedTheElementAValueStandsIn() {
        ConstructionPlan.Result result = result(0, someItemFiled(), NONE_OF_THEM);

        ConstructionPlan.Result.Refused refused = assertInstanceOf(
                ConstructionPlan.Result.Refused.class, result,
                () -> "some element of a list kept empty is the model's no: " + result);
        assertInstanceOf(ConstructionPlan.ModelRefusal.NoRoom.class, refused.why());
        assertEquals(ITEMS, refused.why().at());
    }

    @Test
    void aListTheRulesKeepEmptyIsRefusedNothingForAValueReadOffEveryElement() {
        ConstructionPlan.Result result = result(0, everyItemFiled(), NONE_OF_THEM);

        assertFalse(result instanceof ConstructionPlan.Result.Refused,
                () -> "a list holding none meets every element being filed: " + result);
    }

    /** A key handed on from inside some entry plans the key, and not the value filed under it. */
    @Test
    void aKeyHandedOnPlansTheKeyOfTheEntry() {
        ConstructionPlan.Held held = assertInstanceOf(ConstructionPlan.Held.class,
                planned(1, someEntryFiled(FILED.key()), ANY).at(FILED));

        assertTrue(held.key().isPresent(), () -> "the key is planned: " + held);
        assertTrue(held.under().isEmpty(), () -> "and the value under it is not: " + held);
    }

    /** A value handed on from inside some entry plans the value, and not its key. */
    @Test
    void aValueHandedOnPlansTheValueOfTheEntry() {
        ConstructionPlan.Held held = assertInstanceOf(ConstructionPlan.Held.class,
                planned(1, someEntryFiled(FILED.element().then("sku")), ANY)
                        .at(FILED));

        assertTrue(held.under().isPresent(), () -> "the value is planned: " + held);
        assertTrue(held.key().isEmpty(), () -> "and the key is not: " + held);
    }

    private static ConstructionPlan.ContentsComposed someEntryFiled(TermPath value) {
        return composedUnder(
                asked(new RowDemand.Exists(FILED, only(keyedInTheShelf(value)), HOLDING,
                        Optional.empty())),
                "filed");
    }

    /** What an element asked only {@code asked} meets. */
    private static RowDemand.AnElementMeets only(RowDemand.OfAnElement asked) {
        return RowDemand.AnElementMeets.only(List.of(asked));
    }

    private static ConstructionPlan planned(int parameter,
                                            ConstructionPlan.ContentsComposed contents,
                                            ConstructionPlan.WhatItMayHold howMany) {
        ConstructionPlan.Result result = result(parameter, contents, howMany);
        return assertInstanceOf(ConstructionPlan.Result.Planned.class, result,
                () -> "a plan is made: " + result).plan();
    }

    private static ConstructionPlan.Result result(int parameter,
                                                  ConstructionPlan.ContentsComposed contents,
                                                  ConstructionPlan.WhatItMayHold howMany) {
        Symbols symbols = READ.symbols();
        return ConstructionPlan.of(READ.types().get(parameter),
                TermPath.of(List.of("items", "filed").get(parameter)),
                ScopedDeclarations.wrapsOf(symbols), symbols, ScopedDeclarations.kindsOf(symbols),
                ScopedDeclarations.sumsOf(symbols), Set.of(), Requirements.NONE, contents,
                howMany);
    }

    private record Read(List<Type> types, Symbols symbols) {}

    /** The declarations, read once: every plan here is asked of the same model. */
    private static final Read READ = read();

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("pick")).findFirst().orElseThrow();
        return new Read(sigs.get(spec.name()).inputTypes(),
                Scopes.derived(compilation.db(), module).value());
    }
}
