package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
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

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

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
     * are different values there; one gathering every element of a set at each holds as many as
     * differ among all of theirs.
     */
    @Test
    void whatAWalkGathersIntoASetIsHowManyDifferentValuesItGathers() {
        assertEquals(theOnlyNumber("variedItems"), theOnlyNumber("gatheredItems"));
        assertEquals(new Quantity.HowManyDifferent(new DecisionSubject.AnInput(TAGS),
                new DecisionSubject.AnInput(TAGS.element().element())), theOnlyNumber("joined"));
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
