package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
            data Item = { price: Int, tag: String?, parts: List<Int> }
            data Box = { xs: List<Int>, items: List<Item>, others: List<Item>, open: Bool, x: Int,
                         y: Int, m: Map<String, Int>, s: String }
            let chosen (b: Box) = if b.open then b.items else []
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
     * Some element of a list chosen by cases meeting a statement is some element of the list the
     * case taken answers meeting it, and a list written empty has none: every element meeting it is
     * the case that answers nothing, or every element of the other meeting it. Chosen where the
     * quantifier is written, under a name, or in a body a call reads, it is one statement.
     */
    @Test
    void aQuantifierOverAListChosenByCasesIsReadInEachCase() {
        Proposition every = stated("Bool.not(b.open) || List.all(i -> i.price >= 1, b.items)");
        Proposition some = stated("b.open && List.any(i -> i.price >= 1, b.items)");
        for (String chosen : List.of("if b.open then b.items else []", "chosen(b)",
                "{ let xs = if b.open then b.items else []\n xs }")) {
            assertEquals(every, stated("List.all(i -> i.price >= 1, " + chosen + ")"), chosen);
            assertEquals(some, stated("List.any(i -> i.price >= 1, " + chosen + ")"), chosen);
        }
        assertEquals(stated("""
                        (Bool.not(b.open) || List.all(i -> i.price >= 1, b.items))
                            && (b.open || List.all(i -> i.price >= 1, b.others))"""),
                stated("List.all(i -> i.price >= 1, if b.open then b.items else b.others)"),
                "the element handed the closure in each case is one of the list that case chose");
    }

    /**
     * A list chosen by cases whose arms are written out holds each arm's elements where that arm is
     * taken: an element of the arm a run does not take meets nothing there. Handed to a walk's
     * parameter first, the elements are the same ones.
     */
    @Test
    void anElementOfAnArmWrittenOutMeetsAStatementOnlyWhereItsArmIsTaken() {
        Proposition byCases = stated("(b.open && b.x == 1) || (Bool.not(b.open) && b.y == 1)");
        assertEquals(byCases, stated("List.any(v -> v == 1, if b.open then [ b.x ] else [ b.y ])"));
        assertEquals(byCases, stated(
                "List.any(v -> v == 1, List.flatMap(e -> [ e ], if b.open then [ b.x ] else [ b.y ]))"));
    }

    /**
     * A list chosen by cases holds every element of the list one case answers only on that case: on
     * the other it holds none, so a total over it is no total of everything that list holds. A list
     * that every case answers is.
     */
    @Test
    void aTotalOverAListChosenByCasesIsNoTotalOfTheListOneCaseChose() {
        String total = "List.fold((acc, x) -> acc + x, 0, %s) >= 10";
        for (String other : List.of("[]", "[1]")) {
            assertEquals(stated("(b.open && " + total.formatted("b.xs") + ") || (Bool.not(b.open)"
                            + " && " + total.formatted(other) + ")"),
                    stated(total.formatted("if b.open then b.xs else " + other)),
                    "on a closed box the total is the other list's, whatever b.xs holds");
        }
        assertEquals(stated(total.formatted("b.xs")),
                stated(total.formatted("if b.open then b.xs else b.xs")),
                "a list every case answers is that list on every run");
    }

    /**
     * A string put together from the words or the characters of another holds something where some
     * of them does, and each of them holds something; so it holds something where the other falls
     * into any, whatever stands between them. A case mapping before it keeps whether there is a
     * code point that is not whitespace.
     */
    @Test
    void aStringMadeOfTheWordsOrCharactersOfAnotherHoldsSomethingWhereThatOneHasAny() {
        Proposition aWord = stated("Bool.not(String.isEmpty(String.trim(b.s)))");
        for (String made : List.of("String.join(\"-\", String.words(b.s))",
                "String.join(\"\", String.words(b.s))",
                "String.join(\"-\", String.words(String.lowercase(b.s)))",
                "String.concat(String.words(String.uppercase(b.s)))")) {
            assertEquals(aWord, stated("String.length(" + made + ") >= 1"), made);
            assertEquals(aWord.denied(), stated("String.isEmpty(" + made + ")"), made);
        }
        assertEquals(stated("String.length(b.s) >= 1"),
                stated("String.length(String.concat(String.characters(b.s))) >= 1"));
    }

    /**
     * What every word is, asked of a word a closure is handed, is what it is asked of the element:
     * it comes out the same for every word, so some word meeting it is the string having one where
     * it holds and none where it fails, and every word meets it.
     */
    @Test
    void whatEveryWordIsIsAskedTheSameOfAClosuresParameter() {
        Proposition aWord = stated("Bool.not(String.isEmpty(String.trim(b.s)))");
        assertEquals(aWord,
                stated("List.any(w -> Bool.not(String.isEmpty(w)), String.words(b.s))"));
        assertEquals(aWord, stated("List.any(w -> String.length(w) >= 1, String.words(b.s))"));
        assertEquals(stated("String.length(b.s) >= 1"), stated(
                "List.any(c -> Bool.not(String.isEmpty(c)), String.characters(b.s))"));
        assertEquals(new Proposition.Always(false),
                stated("List.any(w -> String.isEmpty(w), String.words(b.s))"));
        assertEquals(new Proposition.Always(true),
                stated("List.all(w -> Bool.not(String.isEmpty(w)), String.words(b.s))"));
    }

    /**
     * What every word is says nothing of a word but that it holds something, and a case mapping
     * keeps whether there is a code point that is not whitespace and not how many there are.
     */
    @Test
    void whatEveryWordIsAndWhatAMappingKeepsSayNothingMore() {
        Proposition aWord = stated("Bool.not(String.isEmpty(String.trim(b.s)))");
        for (String more : List.of("List.any(w -> String.length(w) >= 2, String.words(b.s))",
                "String.length(String.lowercase(b.s)) >= 2",
                "List.length(String.words(String.lowercase(b.s))) >= 2")) {
            assertInstanceOf(Proposition.Unread.class, stated(more), more);
        }
        assertNotEquals(aWord,
                stated("String.length(String.join(\"-\", String.split(\",\", b.s))) >= 1"),
                "a piece a split leaves may hold nothing");
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

    /**
     * How many a list made of others holds is a number of those others, however it is made, and
     * one number that arithmetic adds to another. What a closure answers as many of for every
     * element as for any other adds up to that many times how many elements there are; lists
     * written out add up to what each of them holds; and a mapping holds as many as it mapped,
     * whether its closure reads a place of the element or works something out of it.
     */
    @Test
    void howManyAListMadeOfOthersHoldsIsANumberOfThoseOthers() {
        String sum = "List.length(%s) + List.length(b.items) >= 1";
        Proposition once = stated(sum.formatted("b.xs"));
        for (String made : List.of("List.flatMap(e -> [e], b.xs)",
                "List.flatMap(e -> [e + 1], b.xs)", "List.map(e -> e, b.xs)",
                "List.map(e -> e + 1, b.xs)", "{ let ys = List.flatMap(e -> [e], b.xs)\n ys }")) {
            assertEquals(once, stated(sum.formatted(made)), made);
        }
        // A walk adding one for every element counts them, and one adding two counts them twice;
        // so does a walk putting one more in what it carries, and one that doubles what it
        // carries is no count of anything.
        assertEquals(once, stated(
                "List.fold((acc, e) -> acc + 1, 0, b.xs) + List.length(b.items) >= 1"));
        assertEquals(once, stated(sum.formatted("List.fold((acc, e) -> acc ++ [e], [], b.xs)")));
        assertInstanceOf(Proposition.Unread.class,
                stated(sum.formatted("List.fold((acc, e) -> acc ++ acc ++ [e], [], b.xs)")));
        Proposition twice = stated(
                "List.length(b.xs) + List.length(b.xs) + List.length(b.items) >= 1");
        assertEquals(twice, stated(
                "List.fold((acc, e) -> acc + 2, 0, b.xs) + List.length(b.items) >= 1"));
        for (String made : List.of("List.flatMap(e -> [e, e], b.xs)", "List.append(b.xs, b.xs)",
                "List.concat([b.xs, b.xs])")) {
            assertEquals(twice, stated(sum.formatted(made)), made);
        }
        assertEquals(stated("0 + List.length(b.items) >= 1"),
                stated(sum.formatted("List.flatMap(e -> [], b.xs)")));
        assertEquals(stated("List.length(b.xs) + 2 + List.length(b.items) >= 1"),
                stated(sum.formatted("List.concat([b.xs, [1, 2], []])")));
        assertEquals(stated("4 + List.length(b.items) >= 1"),
                stated(sum.formatted("List.flatMap(e -> [e, e], [b.x, b.y])")));
        for (String mapped : List.of("i -> i.price", "i -> i.price + 1", "i -> i")) {
            assertEquals(new Proposition.Always(true), stated(
                    "List.length(List.map(" + mapped + ", b.items)) == List.length(b.items)"),
                    mapped);
        }
    }

    /**
     * A closure answering as many as the element it is handed says is summed over the elements,
     * which is how many occurrences of what those lists hold there are in all, the same number
     * however the lists are put end to end. One answering a number by cases is no
     * number of how many elements there are, and is not read as one.
     */
    @Test
    void whatAClosureAnswersAsManyOfAsTheElementSaysIsNoMultipleOfTheElements() {
        Proposition flattened = stated("List.length(List.flatMap(i -> i.parts, b.items))"
                + " + List.length(b.xs) >= 1");
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, flattened);
        assertTrue(((Relation.Affine) compared.relation()).form().coefs().keySet().stream()
                        .anyMatch(number -> number instanceof DecisionAtom.OfTheInput(
                                NumericTerm.TakenOver over)
                                && over.source().equals(new RunSource.FlattenedOccurrences(
                                        TermPath.of("b").then("items").element().then("parts")
                                                .element()))),
                () -> "every part of every item: " + flattened);
        assertEquals(stated("List.length(List.concat(List.map(i -> i.parts, b.items)))"
                + " + List.length(b.xs) >= 1"), flattened);
        // And the sizes of those lists added up are the same number, by a total or by a fold.
        for (String added : List.of("List.sum(List.map(i -> List.length(i.parts), b.items))",
                "List.fold((acc, i) -> acc + List.length(i.parts), 0, b.items)",
                "List.length(List.fold((acc, i) -> acc ++ i.parts, [], b.items))")) {
            assertEquals(flattened, stated(added + " + List.length(b.xs) >= 1"), added);
        }
        // One answering a number by cases holds, for each case, that many for every element
        // taking it: how many elements meet the case, as a filter keeping them counts them.
        assertEquals(stated("List.length(List.filter(e -> e > 0, b.xs))"
                        + " + List.length(b.items) >= 1"),
                stated("List.length(List.flatMap(e -> if e > 0 then [e] else [], b.xs))"
                        + " + List.length(b.items) >= 1"));
        assertEquals(stated("List.length(List.filter(e -> e > 0, b.xs))"
                        + " + 2 * List.length(List.filter(e -> e <= 0, b.xs))"
                        + " + List.length(b.items) >= 1"),
                stated("List.length(List.flatMap(e -> if e > 0 then [e] else [e, e], b.xs))"
                        + " + List.length(b.items) >= 1"));
    }

    /**
     * A sum over the elements is spread over what each element adds: a sum of a number and a
     * constant is the sum of the number and the constant times how many elements there are, and a
     * sum of twice a number is twice its sum. Two spellings of one sum are one number, so a
     * comparison of them settles.
     */
    @Test
    void aSumOfWhatEachElementAddsIsTheSumOfEachPartOfIt() {
        String parts = "List.length(List.flatMap(i -> i.parts, b.items))";
        assertEquals(new Proposition.Always(true), stated(
                "List.length(List.flatMap(i -> List.append(i.parts, [1]), b.items)) == "
                        + parts + " + List.length(b.items)"));
        assertEquals(new Proposition.Always(true), stated(
                "List.length(List.flatMap(i -> List.append(i.parts, i.parts), b.items)) == 2 * "
                        + parts));
    }

    /**
     * An element a closure is handed inside a number is summed over, so it is no element the
     * comparison is read of: two sums over one container in one comparison are two numbers, and
     * not two elements of the container.
     */
    @Test
    void twoSumsOverOneContainerAreReadInOneComparison() {
        assertEquals(stated("2 * List.sum(List.map(i -> i.price, b.items)) >= 1"),
                stated("List.sum(List.map(i -> i.price, b.items))"
                        + " + List.sum(List.map(j -> j.price, b.items)) >= 1"));
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
     * A closure's parameter is a different value for each element it is handed: on each
     * application it is the one handed, and some element meeting it and every element meeting it
     * are some and every one of those.
     */
    @Test
    void aClosuresParameterIsTheValueEachApplicationHandsIt() {
        Proposition.Any some = assertInstanceOf(Proposition.Any.class,
                stated("List.any(v -> { let y = Int.floorMod(b.x, 7)\n v > y }, [1, 5])"));
        Proposition.All every = assertInstanceOf(Proposition.All.class,
                stated("List.all(v -> { let y = Int.floorMod(b.x, 7)\n v > y }, [1, 5])"));
        for (List<Proposition> parts : List.of(some.parts(), every.parts())) {
            assertEquals(2, parts.size(), () -> "one statement per value written: " + parts);
            assertEquals(1, parts.stream()
                    .map(part -> ((Relation.Affine) ((Proposition.Compared) part).relation())
                            .form().coefs().keySet())
                    .distinct().count(), () -> "each about the one value y is: " + parts);
        }
    }

    /**
     * A value the body works out from the parameter is another value on each application, so it is
     * no one value to relate: what each application states of it is what the same comparison
     * written out states there, and its binding names none of them.
     */
    @Test
    void aValueWorkedOutFromTheParameterIsNoOneValue() {
        for (String over : List.of("List.any", "List.all")) {
            assertEquals(stated(over + "(v -> Int.floorMod(v - b.x, 7) > 3, [1, 5])"),
                    stated(over + "(v -> { let y = Int.floorMod(v - b.x, 7)\n y > 3 }, [1, 5])"),
                    over);
        }
    }

    /** What the domain has no words for is not carried, whichever way it is asked. */
    @Test
    void whatTheDomainHasNoWordsForIsNotCarried() {
        assertInstanceOf(Proposition.Unread.class,
                stated("String.isEmpty(String.replace(\"a\", \"b\", b.s))"));
        assertInstanceOf(Proposition.Unread.class,
                stated("String.length(String.replace(\"a\", \"b\", b.s)) >= 1"));
        assertInstanceOf(Proposition.Unread.class,
                stated("String.length(String.replace(\"a\", \"b\", b.s)) == 0"));
    }

    /** Two parts nothing read are two parts. */
    @Test
    void twoUnreadPartsAreNotOne() {
        Proposition two = stated("String.isEmpty(String.replace(\"a\", \"b\", b.s))"
                + " && String.isEmpty(String.replace(\"c\", \"d\", b.s))");
        Proposition.All all = assertInstanceOf(Proposition.All.class, two);
        assertEquals(2, all.parts().size());
    }

    /**
     * The cases of one condition are one statement whichever way they are written: an {@code if}
     * on it, a list chosen by it, each case joined to its condition by "and" and the two by "or",
     * and what follows from the condition and from its denial joined by "and".
     */
    @Test
    void theCasesOfAConditionAreOneStatementInEverySpelling() {
        String every = "i -> i.price >= 1";
        Proposition chosen = stated("List.all(" + every
                + ", if b.open then b.items else b.others)");
        assertEquals(chosen, stated("if b.open then List.all(" + every + ", b.items)"
                + " else List.all(" + every + ", b.others)"));
        assertEquals(chosen, stated("(b.open && List.all(" + every + ", b.items))"
                + " || (Bool.not(b.open) && List.all(" + every + ", b.others))"));
        assertEquals(chosen, stated("(Bool.not(b.open) || List.all(" + every + ", b.items))"
                + " && (b.open || List.all(" + every + ", b.others))"));
    }

    /** What the condition of {@code f}'s one fork states, its fork written as {@code condition}. */
    private static Proposition stated(String condition) {
        String model = "module demo\n\n" + INPUT + """

                behavior f : (b: Box) -> Int
                let f (b) = if %s then 1 else 0
                """.formatted(condition);
        Compilation compilation = Compilation.ofSource(model, "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        // The errors of what was asked, which is the body checked: a model that does not check
        // has no fork to read, whatever its condition says.
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + condition);
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
