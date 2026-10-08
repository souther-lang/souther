package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a condition states is one proposition however it is written, and is carried back through
 * the values a body derives to what the input holds.
 *
 * <p>Each model below is a behavior forking on one condition, and what is compared is the
 * proposition its condition comes to: two spellings of one statement come to one, and a derived
 * value comes to a statement about the positions it was derived from — through a filter, a mapping,
 * a filterMap and a branch alike, and through all of them at once.
 */
class WhatAConditionStatesIsTheSameHoweverItIsSpeltTest {

    private static final String INPUT = """
            data Item = { price: Int, tag: String? }
            data Box = { xs: List<Int>, items: List<Item>, open: Bool, x: Int, y: Int,
                         m: Map<String, Int> }
            """;

    @Test
    void anEmptinessOfAPositionIsOneStatementInEverySpelling() {
        Proposition empty = stated("List.isEmpty(b.xs)");
        assertEquals(empty, stated("List.length(b.xs) == 0"));
        assertEquals(empty, stated("List.length(b.xs) < 1"));
        assertEquals(empty, stated("List.length(b.xs) <= 0"));
        assertEquals(empty.denied(), stated("List.length(b.xs) >= 1"));
        assertEquals(empty.denied(), stated("List.length(b.xs) /= 0"));
        assertEquals(empty.denied(), stated("Bool.not(List.isEmpty(b.xs))"));
        assertInstanceOf(Proposition.Compared.class, empty, "a statement about the size");
    }

    @Test
    void aDenialIsOneStatementInEverySpelling() {
        assertEquals(stated("b.x > 0").denied(), stated("Bool.not(b.x > 0)"));
        assertEquals(stated("Bool.not(b.x > 0)"), stated("(b.x > 0) == false"));
        assertEquals(stated("b.x > 0").denied(), stated("b.x <= 0"));
    }

    @Test
    void theOrderAndTheRepetitionOfWhatIsJoinedSayNothing() {
        assertEquals(stated("b.x > 0 && b.y > 0"), stated("b.y > 0 && b.x > 0"));
        assertEquals(stated("b.x > 0"), stated("b.x > 0 || b.x > 0"));
        assertNotEquals(stated("b.x > 0 && b.y > 0"), stated("b.x > 0 || b.y > 0"));
    }

    @Test
    void whatAFilterKeptHoldingSomethingIsSomeElementMeetingItsClosure() {
        Proposition some = stated("List.any(v -> v > 0, b.xs)");
        assertInstanceOf(Proposition.Some.class, some);
        assertEquals(some, stated("Bool.not(List.isEmpty(List.filter(v -> v > 0, b.xs)))"));
        assertEquals(some, stated("List.length(List.filter(v -> v > 0, b.xs)) >= 1"));
        assertEquals(some, stated("List.length(List.filter(v -> v > 0, b.xs)) > 0"));
        assertEquals(some.denied(), stated("List.all(v -> v <= 0, b.xs)"));
    }

    /**
     * What no element decides comes out of the quantifier: some element meeting it is it and the
     * container holding something. Left inside, the container would be something the proposition
     * turns on that no part of it names — a truth that holds makes the walk whether there is an
     * element, and one that fails makes it false.
     */
    @Test
    void whatNoElementDecidesIsNoPartOfWhatSomeElementMeets() {
        String fixed = "String.startsWith(\"a\", \"ab\")";
        assertEquals(stated(fixed + " && Bool.not(List.isEmpty(b.xs))"),
                stated("List.any(v -> " + fixed + ", b.xs)"));
        assertEquals(stated(fixed + " && Bool.not(List.isEmpty(b.xs))"),
                stated("Bool.not(List.isEmpty(List.filter(v -> " + fixed + ", b.xs)))"));
        assertEquals(stated("(" + fixed + " && Bool.not(List.isEmpty(b.xs))) || List.any(v -> v > 0, b.xs)"),
                stated("List.any(v -> " + fixed + " || v > 0, b.xs)"),
                "a disjunction is some element meeting one part or some element meeting the other");
        assertEquals(stated(fixed + " && List.any(v -> v > 0, b.xs)"),
                stated("List.any(v -> " + fixed + " && v > 0, b.xs)"),
                "a part no element decides comes out of a conjunction the element does");
    }

    @Test
    void aMappingHoldsSomethingWhereWhatItMappedDoes() {
        assertEquals(stated("List.isEmpty(List.filter(v -> v > 0, b.xs))"),
                stated("List.isEmpty(List.map(v -> v + 1, List.filter(v -> v > 0, b.xs)))"));
        assertEquals(stated("List.isEmpty(b.xs)"),
                stated("List.isEmpty(List.reverse(b.xs))"));
    }

    @Test
    void aBranchBuildingAListHoldsSomethingWhereTheArmTakenDoes() {
        Proposition branch = stated(
                "Bool.not(List.isEmpty(if b.open then b.xs else []))");
        assertEquals(Proposition.all(List.of(stated("b.open"),
                stated("Bool.not(List.isEmpty(b.xs))"))), branch);
    }

    /**
     * The three at once, the way a body writes them: a list built under a branch, mapped from what a
     * filterMap kept of the items, holds something where the branch is taken and some item holds a
     * tag.
     */
    @Test
    void theStepsCompose() {
        Proposition composed = stated("""
                Bool.not(List.isEmpty(if b.open
                    then List.map(t -> String.length(t), List.filterMap(i -> i.tag, b.items))
                    else []))""");
        Proposition.All all = assertInstanceOf(Proposition.All.class, composed);
        assertTrue(all.parts().contains(stated("b.open")), () -> "the branch: " + all);
        Proposition.Some some = all.parts().stream()
                .filter(Proposition.Some.class::isInstance).map(Proposition.Some.class::cast)
                .findFirst().orElseThrow(() -> new AssertionError("some item: " + all));
        assertEquals("b.items", some.container().toString());
        Proposition.Present tag = assertInstanceOf(Proposition.Present.class,
                some.ofTheElement());
        assertEquals("b.items[*].tag", ((DecisionSubject.AnInput) tag.of()).at().toString());
    }

    /**
     * An entry of a map is its key and its value, so what a filter of its entries asks of either is
     * asked of the element.
     */
    @Test
    void anEntryOfAMapIsTheElementByItsKeyAndByItsValue() {
        for (List<String> asked : List.of(
                List.of("String.length(k) >= 3", "b.m[key]"),
                List.of("v > 0", "b.m[*]"))) {
            Proposition some = stated("Bool.not(Map.isEmpty(Map.filterEntries((k, v) -> "
                    + asked.get(0) + ", b.m)))");
            Proposition.Some entry = assertInstanceOf(Proposition.Some.class, some, asked.get(0));
            assertEquals("b.m", entry.container().toString());
            Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class,
                    entry.ofTheElement(), asked.get(0));
            assertTrue(compared.relation().toString().contains(asked.get(1)),
                    () -> asked.get(0) + " is about " + asked.get(1) + ": " + compared);
        }
    }

    /** One container quantified inside itself would make its two elements one subject. */
    @Test
    void aContainerQuantifiedInsideItselfIsNotRead() {
        Proposition nested = stated("List.any(v -> List.any(w -> v < w, b.xs), b.xs)");
        Proposition.Some outer = assertInstanceOf(Proposition.Some.class, nested);
        assertInstanceOf(Proposition.Unread.class, outer.ofTheElement(),
                "the inner element is not read as the outer one");
    }

    /**
     * A closure's parameter is a different value for each element it is handed, so a relation
     * over it is no relation between two values of one run — and some element meeting it and every
     * element meeting it are not one statement.
     */
    @Test
    void aClosuresParameterIsNoOneValue() {
        for (String over : List.of("List.any", "List.all")) {
            Proposition stated = stated(over
                    + "(v -> { let y = Int.abs(b.x)\n v > y }, [1, 5])");
            assertFalse(stated.toString().contains("Affine"),
                    () -> over + " relates no two values: " + stated);
        }
    }

    /** What the library does not say answers as many, or answers by a witness, is not carried. */
    @Test
    void whatTheLibraryDoesNotSayIsNotCarried() {
        assertInstanceOf(Proposition.Unread.class, stated("List.isEmpty(List.take(1, b.xs))"));
        assertInstanceOf(Proposition.Unread.class,
                stated("List.length(List.filter(v -> v > 0, b.xs)) >= 2"));
        assertInstanceOf(Proposition.Unread.class,
                stated("List.length(List.filter(v -> v > 0, b.xs)) == 1"));
    }

    /** Two parts nothing read are two parts. */
    @Test
    void twoUnreadPartsAreNotOne() {
        Proposition two = stated("List.isEmpty(List.take(1, b.xs)) && List.isEmpty(List.drop(1, b.xs))");
        Proposition.All all = assertInstanceOf(Proposition.All.class, two);
        assertEquals(2, all.parts().size());
    }

    /** What the condition of {@code f}'s one fork states, its fork written as {@code condition}. */
    private static Proposition stated(String condition) {
        String model = "module demo\n\n" + INPUT + """

                behavior f : (b: Box) -> Int
                let f (b) = if %s then 1 else 0
                """.formatted(condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()),
                "the body is the fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty())
                .proposition();
    }
}
