package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many an operation answers, where its law says that is a number taken over the elements of
 * what it was handed, is read as that number: how many different values they come to, or what a
 * number of each adds up to — over the position the container stands at — and not as some other
 * number, or as nothing.
 *
 * <p>How many different values there are is a number no composer writes a container toward, so the
 * run decides a comparison over it; the statement is the one the law says. What the sizes of the
 * lists inside the elements add up to is how many occurrences there are of what those lists hold,
 * a number of a run a row is composed to hold.
 */
class ANumberOverTheElementsIsReadAsTheNumberItIsTest {

    private static final String MODEL = """
            module probe.overElements

            data Shelf = { codes: List<Int>, bins: List<List<Int>>, tags: List<Set<Int>>,
                           left: Int, right: Int }

            behavior varied : (s: Shelf) -> Bool
            let varied (s) = List.length(List.distinct(s.codes)) >= 2

            data WithKey = { key: Int }
            data WithoutKey = { n: Int }
            data Kind = WithKey | WithoutKey

            behavior keyedOnce : (kinds: List<Kind>) -> Bool
            let keyedOnce (kinds) = List.length(List.flatMap(k -> match k with
                | WithKey { key } -> [ key ]
                | WithoutKey -> [], kinds)) >= 2

            behavior keyedTwice : (kinds: List<Kind>) -> Bool
            let keyedTwice (kinds) = List.length(List.flatMap(k -> match k with
                | WithKey { key } -> [ key, key ]
                | WithoutKey -> [ 0 ], kinds)) >= 3

            data Direct = { account: Int }
            data ViaDeal = { account: Int, deal: Int }
            data Elsewhere = { lead: Int }
            data Related = Direct | ViaDeal | Elsewhere

            behavior relatedByEither : (rs: List<Related>) -> Bool
            let relatedByEither (rs) = List.length(List.flatMap(r -> match r with
                | Direct { account } -> [ account ]
                | ViaDeal { account } -> [ account ]
                | Elsewhere -> [], rs)) >= 2

            data Inner = { flag: Bool }
            data Wrapped = Inner
            data Line = { code: Int, n: Int, w: Wrapped }

            behavior lined : (ls: List<Line>) -> Bool
            let lined (ls) = List.length(ls) >= 1

            behavior relatedKept : (rs: List<Related>) -> Bool
            let relatedKept (rs) = List.length(List.filter(r -> match r with
                | Direct -> true
                | ViaDeal -> true
                | Elsewhere -> false, rs)) >= 2

            behavior stocked : (s: Shelf) -> Bool
            let stocked (s) = List.length(List.concat(s.bins)) >= 3

            data Item = { code: Int, bins: List<Int> }

            behavior variedItems : (items: List<Item>) -> Bool
            let variedItems (items) = List.length(List.distinct(List.map(.code, items))) >= 2

            behavior stockedItems : (items: List<Item>) -> Bool
            let stockedItems (items) =
                List.length(List.concat(List.map(.bins, items))) >= 3

            behavior variedOfSome : (items: List<Item>) -> Bool
            let variedOfSome (items) = List.length(List.distinct(
                List.map(.code, List.filter(i -> i.code > 0, items)))) >= 2

            behavior gatheredItems : (items: List<Item>) -> Bool
            let gatheredItems (items) =
                Set.size(List.fold((acc, i) -> Set.insert(i.code, acc), Set.empty, items)) >= 2

            behavior joined : (s: Shelf) -> Bool
            let joined (s) =
                Set.size(List.fold((acc, t) -> Set.union(acc, t), Set.empty, s.tags)) >= 2

            behavior apart : (s: Shelf) -> Bool
            let apart (s) = Set.size(Set.fromList([s.left, s.right])) >= 2

            behavior variedWorkedOut : (items: List<Item>) -> Bool
            let variedWorkedOut (items) =
                List.length(List.distinct(List.map(i -> i.code + 1, items))) >= 2

            behavior keptOfEach : (items: List<Item>) -> Bool
            let keptOfEach (items) = List.length(List.fold(
                (acc, i) -> acc ++ List.filter(b -> b > 0, i.bins), [], items)) >= 3

            behavior keptPastWhatWasCarried : (items: List<Item>) -> Bool
            let keptPastWhatWasCarried (items) = List.length(List.fold(
                (acc, i) -> acc ++ List.filter(b -> b > List.length(acc), i.bins), [], items)) >= 3

            behavior keptPastWhatWasCarriedWrittenOut : (s: Shelf) -> Bool
            let keptPastWhatWasCarriedWrittenOut (s) = List.length(List.fold(
                (acc, c) -> acc ++ List.filter(b -> b > List.length(acc), [c]), [], s.codes)) >= 2

            data Forecast = { currency: String, amount: Int }
            data Node = { owner: String, reports: List<Node>, helpers: List<Node> }

            let own (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                Map.get(node.owner, byOwner) |> Option.map(one -> [ one ]) |> Option.withDefault([])

            let under (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ under(r, byOwner), own(node, byOwner), node.reports)

            let underBoth (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ underBoth(r, byOwner),
                          List.fold((acc, r) -> acc ++ underBoth(r, byOwner), own(node, byOwner),
                                    node.reports),
                          node.helpers)

            let underTwice (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ underTwice(r, byOwner) ++ underTwice(r, byOwner),
                          own(node, byOwner), node.reports)

            let underFoldedTwice (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ underFoldedTwice(r, byOwner),
                          List.fold((acc, r) -> acc ++ underFoldedTwice(r, byOwner),
                                    own(node, byOwner), node.reports),
                          node.reports)

            let ownNothing (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                Map.get(node.owner, byOwner) |> Option.map(one -> []) |> Option.withDefault([])

            let underLookingUp (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ underLookingUp(r, byOwner), ownNothing(node, byOwner),
                          node.reports)

            let underWithoutOwn (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ underWithoutOwn(r, byOwner), [], node.reports)

            behavior collected : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collected (node, byOwner) =
                Set.size(Set.fromList(List.map(.currency, under(node, byOwner)))) == 1

            behavior collectedEntries : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedEntries (node, byOwner) =
                List.length(List.distinct(under(node, byOwner))) >= 2

            behavior collectedBothWays : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedBothWays (node, byOwner) =
                Set.size(Set.fromList(List.map(.currency, underBoth(node, byOwner)))) == 1

            behavior collectedTwice : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedTwice (node, byOwner) =
                Set.size(Set.fromList(List.map(.currency, underTwice(node, byOwner)))) == 1

            behavior collectedFoldedTwice : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedFoldedTwice (node, byOwner) =
                Set.size(Set.fromList(List.map(.currency, underFoldedTwice(node, byOwner)))) == 1

            behavior collectedLookedUpOnly : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedLookedUpOnly (node, byOwner) =
                Set.size(Set.fromList(List.map(.currency, underLookingUp(node, byOwner)))) == 1

            behavior collectedNoEntry : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedNoEntry (node, byOwner) =
                Set.size(Set.fromList(List.map(.currency, underWithoutOwn(node, byOwner)))) == 1

            behavior collectedSomeEntries : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedSomeEntries (node, byOwner) = List.length(List.distinct(
                List.filter(f -> f.amount > 0, under(node, byOwner)))) >= 2

            behavior collectedSome : (node: Node, byOwner: Map<String, Forecast>) -> Bool
            let collectedSome (node, byOwner) = Set.size(Set.fromList(List.map(.currency,
                List.filter(f -> f.amount > 0, under(node, byOwner))))) == 1

            """;

    private static final TermPath CODES = TermPath.of("s").then("codes");
    private static final TermPath BINS = TermPath.of("s").then("bins");
    private static final TermPath ITEMS = TermPath.of("items");
    private static final TermPath S = TermPath.of("s");
    private static final TermPath TAGS = S.then("tags");

    @Test
    void howManyADistinctListHoldsIsHowManyDifferentValuesTheListHolds() {
        Quantity read = theOnlyNumber("varied");
        assertEquals(new Quantity.HowManyDifferent(new DecisionSubject.AnInput(CODES),
                new DecisionSubject.AnInput(CODES.element())), read);
    }

    /**
     * How many a flattening holds whose closure answers by the case of each element is, for each
     * arm, how many the arm answers times how many elements take it: a count of the elements
     * taking it, weighed by what it answers.
     */
    @Test
    void howManyAFlatteningByTheCasesOfEachElementHoldsIsHowManyTakeEachArmWeighed() {
        List<OnTheWay> once = statedAll("keyedOnce");
        assertEquals(1, once.size(), () -> "one statement: " + once);
        RowDemand.SoMany taken = assertInstanceOf(RowDemand.SoMany.class,
                assertInstanceOf(OnTheWay.TakenIn.class, once.getFirst()).demand(),
                () -> "a row is composed for how many take the arm: " + once);
        assertEquals("#kinds [kinds[*] is WithKey] GE 2",
                taken.count().spelled() + " " + taken.met() + " " + taken.level());
        List<OnTheWay> twice = statedAll("keyedTwice");
        assertEquals(1, twice.size(), () -> "one statement: " + twice);
        RowDemand.ForTheRun run = assertInstanceOf(RowDemand.ForTheRun.class,
                assertInstanceOf(OnTheWay.TakenIn.class, twice.getFirst()).demand());
        LinearForm<Quantity> form = assertInstanceOf(Relation.Affine.class,
                assertInstanceOf(Proposition.Compared.class, run.statement()).relation()).form();
        assertEquals("LinearForm[constant=-3, coefs={#kinds [kinds[*] is WithKey]=2,"
                + " #kinds [kinds[*] is WithoutKey]=1}]", form.toString());
    }

    /**
     * Arms answering as many as each other are taken together: an element takes one arm of a
     * match, so how many take either of two is how many take one added to how many take the
     * other, and that is one count of the elements meeting a statement — the one a filter keeping
     * those elements is read by.
     */
    @Test
    void armsAnsweringAsManyAsEachOtherAreCountedAsTheElementsTakingEither() {
        List<OnTheWay> either = statedAll("relatedByEither");
        assertEquals(1, either.size(), () -> "one statement: " + either);
        RowDemand.SoMany taken = assertInstanceOf(RowDemand.SoMany.class,
                assertInstanceOf(OnTheWay.TakenIn.class, either.getFirst()).demand(),
                () -> "a row is composed for how many take either arm: " + either);
        assertEquals("#rs [any[rs[*] is Direct, rs[*] is ViaDeal]] GE 2",
                taken.count().spelled() + " " + taken.met() + " " + taken.level());
        List<OnTheWay> kept = statedAll("relatedKept");
        assertEquals(1, kept.size(), () -> "one statement: " + kept);
        assertEquals(taken, assertInstanceOf(OnTheWay.TakenIn.class, kept.getFirst()).demand());
    }

    /**
     * What the elements of each key come to among those a statement keeps is read of each element
     * whole, and the statement is put to it there: so what is worn on the way to a place the
     * statement reads is said, as it is for the places the key and the number read.
     */
    @Test
    void whatIsWornOnTheWayToAPlaceTheStatementKeepingTheElementsReadsIsSaid() {
        TermPath lines = TermPath.of("ls");
        Proposition flagged = new Proposition.Present(
                new DecisionSubject.AnInput(lines.element().then("w").then("flag")), true);
        KeptOccurrences kept = new KeptOccurrences(new DecisionSubject.AnInput(lines), flagged,
                AStatementAtARow.of(flagged, "lined", null));
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get("lined");
        Quantities quantities = inputs.reading(rules()).quantities();
        ElementProjection wrapped = ElementProjection.ofFields(List.of("w"));
        List<String> worn = new ArrayList<>();
        for (KeptOccurrences selection : Arrays.asList(kept, null)) {
            NumericTerm.GatheredUnderItsKey total = NumericTerm.GatheredUnderItsKey.of(
                    lines.element(), new ElementKey.At(ElementProjection.ofFields(List.of("code"))),
                    new ElementValue.Affine(LinearForm.atom(ElementProjection.ofFields(
                            List.of("n")))), Type.Prim.INT,
                    NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, selection);
            worn.add(quantities.ordersOf(total).wornAt(wrapped).toString());
        }
        assertTrue(worn.getFirst().contains("Wrapped"), worn::toString);
        assertEquals("[]", worn.getLast(), "nothing reads past the field where nothing keeps them");
    }

    @Test
    void howManyListsPutEndToEndHoldIsHowManyOccurrencesOfTheirElementsThereAre() {
        assertEquals(BINS.element().element(), theOccurrencesCounted("stocked"));
    }

    @Test
    void howManyDifferentValuesAMappedListHoldsIsHowManyDifferentValuesOfWhatIsTakenOfEach() {
        assertEquals(new Quantity.HowManyDifferent(new DecisionSubject.AnInput(ITEMS),
                new DecisionSubject.AnInput(ITEMS.element().then("code"))),
                theOnlyNumber("variedItems"));
    }

    /**
     * A walk gathering into a set the value at a place of each element ends with as many as there
     * are different values there: an insert's laws say how many its answer holds and which. One
     * gathering every element of a set at each by a union is not read so — a union's law says how
     * many and nothing says which.
     */
    @Test
    void whatAWalkGathersIntoASetIsHowManyDifferentValuesItGathers() {
        assertEquals(theOnlyNumber("variedItems"), theOnlyNumber("gatheredItems"));
        List<OnTheWay> joined = statedAll("joined");
        assertEquals(1, joined.size(), joined::toString);
        assertInstanceOf(OnTheWay.Declined.class, joined.getFirst());
    }

    /**
     * How many different values there are over the elements of a container is of one value of
     * each: the element, a place inside it, or its key — never a place inside a container inside
     * it, which is as many values as that one holds.
     */
    @Test
    void howManyDifferentIsOfOneValueOfEachElement() {
        DecisionSubject tags = new DecisionSubject.AnInput(TAGS);
        DecisionSubject items = new DecisionSubject.AnInput(ITEMS);
        assertTrue(Quantity.HowManyDifferent.oneOfEach(tags,
                new DecisionSubject.AnInput(TAGS.element())));
        assertTrue(Quantity.HowManyDifferent.oneOfEach(items,
                new DecisionSubject.AnInput(ITEMS.element().then("code"))));
        assertFalse(Quantity.HowManyDifferent.oneOfEach(tags,
                new DecisionSubject.AnInput(TAGS.element().element())));
        assertFalse(Quantity.HowManyDifferent.oneOfEach(items,
                new DecisionSubject.AnInput(ITEMS.element().then("bins").element())));
        assertThrows(IllegalArgumentException.class, () -> new Quantity.HowManyDifferent(tags,
                new DecisionSubject.AnInput(TAGS.element().element())));
    }

    /**
     * Two values written out come to two where they differ and one where they do not, so holding
     * how many there are at two is asking a row to hold the two apart — what {@code a /= b}
     * asks.
     */
    @Test
    void howManyDifferentValuesTwoPositionsWrittenOutComeToIsWhetherTheyDiffer() {
        List<OnTheWay> stated = statedAll("apart");
        assertEquals(1, stated.size(), () -> "one statement: " + stated);
        RowDemand.OneValueAtBoth apart = assertInstanceOf(RowDemand.OneValueAtBoth.class,
                assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst()).demand());
        assertFalse(apart.same(), () -> "held apart: " + apart);
        assertEquals(Set.of(S.then("left"), S.then("right")), Set.of(apart.one(), apart.other()));
    }

    @Test
    void whatTheListsOfAMappedListHoldIsEveryOccurrenceOfTheirElementsInTheSource() {
        assertEquals(ITEMS.element().then("bins").element(),
                theOccurrencesCounted("stockedItems"));
    }

    /**
     * Where every occurrence of what {@code behavior}'s condition counts stands, as the row is
     * composed for it: one count of a run no one container holds, against a number written out.
     */
    private static TermPath theOccurrencesCounted(String behavior) {
        List<OnTheWay> stated = statedAll(behavior);
        assertEquals(1, stated.size(), () -> "one statement: " + stated);
        RowDemand.Relational composed = assertInstanceOf(RowDemand.Relational.class,
                assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst()).demand(),
                () -> "a row is composed for it: " + stated);
        LinearForm<NumericTerm> form = assertInstanceOf(TakenConstraint.Affine.class,
                composed.constraint()).form();
        assertEquals(1, form.coefs().size(), () -> "one number: " + form);
        NumericTerm.TakenOver count = assertInstanceOf(NumericTerm.TakenOver.class,
                form.coefs().keySet().iterator().next());
        assertInstanceOf(TakenAs.HowManyItHolds.class, count.takenAs());
        return assertInstanceOf(RunSource.FlattenedOccurrences.class, count.source())
                .subjectPath();
    }

    /**
     * Which of the elements a filter kept is a number of those, which no quantity of the
     * container says; and what a closure worked out of an element is no place of the input.
     */
    @Test
    void aNumberOfSomeOfTheElementsOrOfAValueWorkedOutOfThemIsNoNumberOfTheContainer() {
        assertEquals(List.of(), numbersAsked("variedOfSome"));
        assertEquals(List.of(), numbersAsked("variedWorkedOut"));
    }

    /**
     * A walk's step that keeps some of each element's values is read with what it carried standing
     * for any number, and adds how many it kept of each. One keeping them by how many it carried
     * adds a number of no one size — one at every step, as many as were carried then — so it is
     * no number of each element, wherever in what it adds that number is read.
     */
    @Test
    void aStepAddingANumberOfWhatItCarriedIsNoNumberOfEachElement() {
        assertFalse(numbersAsked("keptOfEach").isEmpty(), "the control is read");
        assertEquals(List.of(), numbersAsked("keptPastWhatWasCarried"));
        assertEquals(List.of(), numbersAsked("keptPastWhatWasCarriedWrittenOut"));
    }

    /**
     * What a search down a tree collects of the entries of a map by the key of each node it
     * reaches is counted as the nodes it reaches and the entries their keys pick, and stands at no
     * place of the map: it is the same number for an entry no node names, whatever that entry
     * holds.
     */
    @Test
    void howManyDifferentValuesASearchCollectsIsOfTheEntriesTheNodesItReachesPick() {
        TermPath node = TermPath.of("node");
        TermPath byOwner = TermPath.of("byOwner");
        assertEquals(new Quantity.HowManyDifferentBelow(node, List.of("reports"), byOwner,
                List.of("owner"), List.of("currency")), theOnlyNumber("collected"));
        assertEquals(new Quantity.HowManyDifferentBelow(node, List.of("reports"), byOwner,
                List.of("owner"), List.of()), theOnlyNumber("collectedEntries"));
    }

    /** Each field the search goes down is gone down once, the entries of the nodes below it
     *  collected whichever field they are below. */
    @Test
    void aSearchGoingDownSeveralFieldsCollectsFromTheNodesBelowEachOnce() {
        assertEquals(new Quantity.HowManyDifferentBelow(TermPath.of("node"),
                List.of("helpers", "reports"), TermPath.of("byOwner"), List.of("owner"),
                List.of("currency")), theOnlyNumber("collectedBothWays"));
    }

    /**
     * A search that goes below a field twice collects what is below it as often, which the
     * collection of each node once does not say; one that collects no entry of its own has nothing
     * to count; and the entries some of them were kept by something are some of the entries, which
     * a number of every node's entry is not.
     */
    @Test
    void aSearchThatIsNotTheEntriesOfEachNodeOnceIsNotCountedAsThat() {
        assertEquals(List.of(), numbersAsked("collectedTwice").stream()
                .filter(Quantity.HowManyDifferentBelow.class::isInstance).toList());
        assertEquals(List.of(), numbersAsked("collectedFoldedTwice").stream()
                .filter(Quantity.HowManyDifferentBelow.class::isInstance).toList());
        assertEquals(List.of(), numbersAsked("collectedLookedUpOnly").stream()
                .filter(Quantity.HowManyDifferentBelow.class::isInstance).toList());
        assertEquals(List.of(), numbersAsked("collectedNoEntry").stream()
                .filter(Quantity.HowManyDifferentBelow.class::isInstance).toList());
        assertEquals(List.of(), numbersAsked("collectedSomeEntries").stream()
                .filter(Quantity.HowManyDifferentBelow.class::isInstance).toList());
        assertEquals(List.of(), numbersAsked("collectedSome").stream()
                .filter(Quantity.HowManyDifferentBelow.class::isInstance).toList());
    }

    /** Every number the conditions {@code behavior} writes are compared over, as the run is asked
     *  them. */
    private static List<Quantity> numbersAsked(String behavior) {
        List<Quantity> out = new ArrayList<>();
        for (OnTheWay each : statedAll(behavior)) {
            if (each instanceof OnTheWay.TakenIn taken
                    && taken.demand() instanceof RowDemand.ForTheRun run
                    && run.statement() instanceof Proposition.Compared compared
                    && compared.relation() instanceof Relation.Affine affine) {
                out.addAll(affine.form().coefs().keySet());
            }
        }
        return out;
    }

    /** The one number besides constants the condition {@code behavior} writes is compared over,
     *  as the run is asked it. */
    private static Quantity theOnlyNumber(String behavior) {
        List<OnTheWay> stated = statedAll(behavior);
        assertEquals(1, stated.size(), () -> "one statement: " + stated);
        RowDemand.ForTheRun run = assertInstanceOf(RowDemand.ForTheRun.class,
                assertInstanceOf(OnTheWay.TakenIn.class, stated.getFirst()).demand(),
                () -> "the run decides it: " + stated);
        assertEquals(RowDemand.NoComposer.A_NUMBER_OVER_ELEMENTS, run.why());
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class,
                run.statement());
        LinearForm<Quantity> form = assertInstanceOf(Relation.Affine.class,
                compared.relation()).form();
        assertEquals(1, form.coefs().size(), () -> "one number: " + form);
        return form.coefs().keySet().iterator().next();
    }

    private static List<OnTheWay> statedAll(String behavior) {
        Bodies.Elaborated checked =
                COMPILATION.db().ask(new Bodies.Checked(module())).value();
        assertNotNull(checked, () -> "the model under test compiles: "
                + COMPILATION.diagnostics().values().stream().flatMap(List::stream)
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                .toList());
        AnalysisBody analysis = checked.analysisBodies().get(behavior);
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs(module())).value()
                .get(behavior);
        InputReading reading = inputs.reading(rules());
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                reading.declared(), ElementBindings.of(analysis, rules().newtypes()),
                inputs.dependencies());
        return ReachingCuts.stating(Condition.of(analysis.core(), reads, rules().symbols(),
                        rules().newtypes(), new ConditionNumbering(module(), behavior,
                                ConditionOccurrence.Reading.DIVIDING)),
                reading, true, WhatConditionsState.of(reading)).entries();
    }

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    private static String module() {
        return COMPILATION.modules().getFirst();
    }

    private static RuleReadingSource rules() {
        return RuleReadings.of(COMPILATION, module());
    }
}
