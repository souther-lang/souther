package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An observation of what an operation answers states what the operation's law says of the
 * arguments it was handed, each part read where it stands.
 *
 * <p>Held against a spelling an author could have written instead, over the arguments themselves:
 * the two coming to one proposition is what says the law was carried across the call and nothing was
 * added or dropped on the way.
 */
class AnObservationOfAnAnswerIsWhatItsLawSaysOfTheArgumentsTest {

    private static final String INPUT = """
            data Box = { xs: List<Int>, ys: List<Int>, n: Int, s: String, t: String, set: Set<Int>,
                         m: Map<String, Int> }
            """;

    /** Asked for some and handed some: a disjunction over the arguments, and not a silence. */
    @Test
    void aTakeHoldsSomethingWhereItWasAskedForSomeAndHandedSome() {
        assertEquals(stated("if b.n >= 1 && List.length(b.xs) >= 1 then 1 else 0"),
                stated("if Bool.not(List.isEmpty(List.take(b.n, b.xs))) then 1 else 0"));
    }

    /** A count below nought drops nothing, so what is left is the list where it holds anything. */
    @Test
    void aDropHoldsSomethingWhereTheListHoldsMoreThanItDrops() {
        assertEquals(stated("if List.length(b.xs) >= 1 && List.length(b.xs) - b.n >= 1 then 1 else 0"),
                stated("if Bool.not(List.isEmpty(List.drop(b.n, b.xs))) then 1 else 0"));
    }

    /** Two lists put end to end, written as the operation or as the operator, hold something where
     *  either does. */
    @Test
    void anAppendHoldsSomethingWhereEitherHalfDoesWrittenEitherWay() {
        Proposition either = stated("if List.length(b.xs) >= 1 || List.length(b.ys) >= 1"
                + " then 1 else 0");
        assertEquals(either, stated("if Bool.not(List.isEmpty(List.append(b.xs, b.ys)))"
                + " then 1 else 0"));
        assertEquals(either, stated("if Bool.not(List.isEmpty(b.xs ++ b.ys)) then 1 else 0"));
        assertEquals(stated("if String.length(b.s) >= 1 || String.length(b.t) >= 1 then 1 else 0"),
                stated("if Bool.not(String.isEmpty(b.s ++ b.t)) then 1 else 0"));
    }

    /**
     * A law naming the element of a container the source wrote out is read of each value it
     * writes, as that value: lists put end to end hold something where one of those written does.
     */
    @Test
    void aLawOverValuesWrittenOutIsReadOfEachOfThem() {
        assertEquals(stated("if List.length(b.xs) >= 1 || List.length(b.ys) >= 1 then 1 else 0"),
                stated("if Bool.not(List.isEmpty(List.concat([b.xs, b.ys]))) then 1 else 0"));
        assertEquals(new Proposition.Always(true),
                stated("if Bool.not(List.isEmpty(List.concat([[1], b.xs]))) then 1 else 0"));
        assertEquals(stated("if String.length(b.s) >= 1 then 1 else 0"),
                stated("if Bool.not(String.isEmpty(String.concat([\"\", b.s]))) then 1 else 0"));
    }

    /** How many values written out meet a statement is a number where each of them settles it,
     *  and which of the rest meet it where one turns on it. */
    @Test
    void aCountOfValuesWrittenOutIsANumberWhereEachSettlesIt() {
        assertEquals(new Proposition.Always(true), stated(
                "if List.length(List.filter(x -> x > 0, [1, 2, -1])) == 2 then 1 else 0"));
        assertEquals(stated("if b.n > 0 then 1 else 0"),
                stated("if List.length(List.filter(x -> x > 0, [b.n, 1])) == 2 then 1 else 0"));
    }

    /**
     * One value written many times is one statement met as many times, however many that is.
     */
    @Test
    void aValueWrittenManyTimesIsOneStatement() {
        String nine = String.join(", ", Collections.nCopies(9, "b.n"));
        assertEquals(stated("if b.n > 0 then 1 else 0"), stated(
                "if List.length(List.filter(x -> x > 0, [" + nine + "])) == 9 then 1 else 0"));
    }

    /**
     * Which of them meet it is read as the choices the comparison admits, written out where they
     * are few, and held as the count where they are more than one condition is read in — read to
     * the end either way. Exactly one of eighteen is a choice for each; half of them is every way
     * of picking nine.
     */
    @Test
    void aCountOfMoreChoicesThanTheReadingsOfACondition() {
        List<String> eighteen = new ArrayList<>();
        for (int i = 0; i < 18; i++) {
            eighteen.add("b.n + " + i);
        }
        String written = "[" + String.join(", ", eighteen) + "]";
        assertNull(Proposition.firstStopIn(stated(
                "if List.length(List.filter(x -> x > 0, " + written + ")) == 1 then 1 else 0")));
        Proposition half = stated(
                "if List.length(List.filter(x -> x > 0, " + written + ")) == 9 then 1 else 0");
        assertNull(Proposition.firstStopIn(half), half::toString);
        assertInstanceOf(Proposition.SoManyHold.class, half);
    }

    /**
     * A count compared by an operation's law and not as written is held the same way: what
     * {@code List.drop} leaves is empty by how many the list holds against how many it drops, so
     * dropping ten of thirty values written out is eleven or more of them kept, every way of
     * picking eleven. Read where the law's comparison is made, it is held as the count — and not
     * written out however many ways that is.
     */
    @Test
    @Timeout(value = 30, threadMode = Timeout.ThreadMode.SEPARATE_THREAD)
    void aCountALawComparesIsHeldTheSameWay() {
        List<String> thirty = new ArrayList<>();
        for (int i = 0; i < 30; i++) {
            thirty.add("b.n + " + i);
        }
        String kept = "List.filter(x -> x > 0, [" + String.join(", ", thirty) + "])";
        Proposition dropped = stated("if List.isEmpty(List.drop(10, " + kept + ")) then 1 else 0");
        assertNull(Proposition.firstStopIn(dropped), dropped::toString);
        assertTrue(holdsACount(dropped), dropped::toString);
        assertNull(Proposition.firstStopIn(stated(
                "if List.isEmpty(List.drop(0, " + kept + ")) then 1 else 0")));
    }

    /** Whether {@code stated} or some part of it is a count of statements held as the count. */
    private static boolean holdsACount(Proposition stated) {
        return stated instanceof Proposition.SoManyHold
                || stated.partsHeld().stream()
                        .anyMatch(AnObservationOfAnAnswerIsWhatItsLawSaysOfTheArgumentsTest::holdsACount);
    }

    /** What a set holds once a value is taken out is some other value, read as the quantifier over
     *  the set's element. */
    @Test
    void aSetWithAValueTakenOutHoldsSomeOtherValue() {
        TermPath set = TermPath.of("b").then("set");
        assertEquals(new Proposition.Some(new DecisionSubject.AnInput(set),new Proposition.SameValue(
                        new DecisionSubject.AnInput(set.element()),
                        new DecisionSubject.AnInput(TermPath.of("b").then("n")), false), true),
                stated("if Bool.not(Set.isEmpty(Set.remove(b.n, b.set))) then 1 else 0"));
    }

    /**
     * A trimmed string being empty comes to every code point of the string being whitespace: how
     * many are not, held against nought. So does a string with no words, and a string lowercased
     * after it was trimmed, which holds something exactly where what it was made of does.
     */
    @Test
    void aTrimmedStringBeingEmptyIsEveryCodePointOfTheStringBeingWhitespace() {
        Proposition stated = stated("if String.isEmpty(String.trim(b.s)) then 1 else 0");
        assertNull(Proposition.firstStopIn(stated));
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, stated);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        assertEquals(List.of("#(not whitespace)(b.s)"), affine.form().coefs().keySet().stream()
                .map(Object::toString).toList(), "the one number it is about");
        assertEquals(stated, stated("if List.isEmpty(String.words(b.s)) then 1 else 0"));
        assertEquals(stated, stated(
                "if String.isEmpty(String.lowercase(String.trim(b.s))) then 1 else 0"));
        assertEquals(stated.denied(), stated(
                "if Bool.not(String.isEmpty(String.trim(b.s))) then 1 else 0"));
    }

    /**
     * How many elements a filter keeps held against nought is whether some element is kept, which
     * the filter's witness law reads the same check as: whichever was written, and whichever rule
     * read it, one proposition.
     */
    @Test
    void aCountHeldAgainstNoughtIsWhetherSomeElementMeetsIt() {
        String count = "List.length(List.filter(x -> x > b.n, b.xs))";
        Proposition some = stated("if Bool.not(List.isEmpty(List.filter(x -> x > b.n, b.xs)))"
                + " then 1 else 0");
        assertInstanceOf(Proposition.Some.class, some);
        for (String atLeastOne : List.of(count + " >= 1", count + " > 0", count + " /= 0",
                "1 <= " + count)) {
            assertEquals(some, stated("if " + atLeastOne + " then 1 else 0"), atLeastOne);
            for (Proposition byARule : byEachRule("if " + atLeastOne + " then 1 else 0")) {
                assertEquals(some, byARule, atLeastOne);
            }
        }
        for (String none : List.of(count + " == 0", count + " < 1", count + " <= 0")) {
            assertEquals(some.denied(), stated("if " + none + " then 1 else 0"), none);
        }
        assertEquals(new Proposition.Always(true), stated("if " + count + " >= 0 then 1 else 0"));
        assertEquals(new Proposition.Always(false), stated("if " + count + " < 0 then 1 else 0"));
    }

    /** Held against any other number, a count says how many, and is kept as the relation. */
    @Test
    void aCountHeldAgainstAnotherNumberSaysHowMany() {
        Proposition exactlyOne = stated(
                "if List.length(List.filter(x -> x > b.n, b.xs)) == 1 then 1 else 0");
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, exactlyOne);
        Relation.Affine relation = assertInstanceOf(Relation.Affine.class, compared.relation());
        assertTrue(relation.form().coefs().keySet().stream()
                        .anyMatch(quantity -> quantity instanceof Quantity.HowManyMeet),
                "the relation is over the count: " + exactlyOne);
        assertNull(Proposition.firstStopIn(stated(
                "if List.length(List.filter(x -> x > 3, b.xs)) >= 2 then 1 else 0")));
    }

    /** What a count is about is the element where it stands, so the name an author gave the
     *  element does not make it another count. */
    @Test
    void aCountIsTheSameWhateverItsElementIsCalled() {
        assertEquals(stated("if List.length(List.filter(x -> x > b.n, b.xs)) == 2 then 1 else 0"),
                stated("if List.length(List.filter(y -> y > b.n, b.xs)) == 2 then 1 else 0"));
        assertNotEquals(stated("if List.length(List.filter(x -> x > b.n, b.xs)) == 2 then 1 else 0"),
                stated("if List.length(List.filter(x -> x > b.n, b.ys)) == 2 then 1 else 0"));
    }

    /** A count of a container inside a statement about some element of that same container would
     *  name two elements one subject, and is not read. */
    @Test
    void aCountInsideAQuantifierOverItsOwnContainerIsNotRead() {
        Proposition nested = stated("if List.any(x -> List.length(List.filter(y -> y > x, b.xs))"
                + " == 1, b.xs) then 1 else 0");
        assertInstanceOf(WhyUnread.TwoElementsOfOneContainer.class,
                Proposition.firstStopIn(nested), nested.toString());
    }

    /**
     * Two lookups in one map, each with a default, added in one comparison: where both keys are
     * filed it is about two entries, which said under one quantifier over the map would be one
     * subject, and it is not read — as the sum of two elements of one container is not, however
     * the two were taken out of it. One lookup beside a number is read.
     */
    @Test
    void twoLookupsInOneMapAreNotReadAsOneEntry() {
        Proposition two = stated("if Option.withDefault(0, Map.get(b.s, b.m))"
                + " + Option.withDefault(0, Map.get(b.t, b.m)) >= b.n then 1 else 0");
        assertInstanceOf(WhyUnread.TwoElementsOfOneContainer.class,
                Proposition.firstStopIn(two), two.toString());

        Proposition one = stated("if Option.withDefault(0, Map.get(b.s, b.m)) >= b.n then 1 else 0");
        assertFalse(Proposition.leavesSomethingUnread(one), one.toString());
    }

    /** How many what a mapping answers holds is how many it was handed, read as that one's size. */
    @Test
    void aSizeOfAMappingIsTheSizeOfWhatItWasHanded() {
        assertEquals(stated("if List.length(b.xs) == 2 then 1 else 0"),
                stated("if List.length(List.map(x -> x + 1, b.xs)) == 2 then 1 else 0"));
        assertEquals(stated("if List.length(b.xs) + List.length(b.ys) == 2 then 1 else 0"),
                stated("if List.length(b.xs ++ b.ys) == 2 then 1 else 0"));
    }

    /**
     * Strings joined, one made of each character or word of a string, hold something where some
     * one of them does — and where what each is made of settles that the same way for every one,
     * that is the string holding a character or a word at all. No element stands at a position
     * of the input, and none needs to: what is asked of it does not turn on which it is. Whether
     * the answer is written the same for each, is the element itself, or is chosen by cases each
     * of which settles it; and through another mapping, another order, or what was kept by a
     * statement every element meets.
     */
    @Test
    void stringsMadeOneForEachCharacterHoldSomethingWhereTheStringHoldsACharacter() {
        Proposition aCharacter = stated(
                "if Bool.not(List.isEmpty(String.characters(b.s))) then 1 else 0");
        Proposition aWord = stated("if Bool.not(List.isEmpty(String.words(b.s))) then 1 else 0");
        assertNull(Proposition.firstStopIn(aCharacter));
        assertNull(Proposition.firstStopIn(aWord));
        assertNotEquals(aCharacter, aWord);
        for (String each : List.of("c -> \" \"", "c -> c", "c -> c ++ b.t",
                "c -> if String.matches(\"[a-z0-9]\", c) then c else \" \"")) {
            assertEquals(aCharacter, stated("if String.length(String.concat(List.map(" + each
                    + ", String.characters(b.s)))) >= 1 then 1 else 0"), each);
            assertEquals(aWord, stated("if String.length(String.concat(List.map(" + each
                    + ", String.words(b.s)))) >= 1 then 1 else 0"), each);
        }
        for (String made : List.of("List.map(d -> d, String.characters(b.s))",
                "List.reverse(String.characters(b.s))",
                "Set.toList(Set.fromList(String.characters(b.s)))",
                "List.filter(c -> String.length(c) >= 1, String.characters(b.s))")) {
            assertEquals(aCharacter, stated("if String.length(String.concat(List.map(c -> \" \", "
                    + made + "))) >= 1 then 1 else 0"), made);
        }
        assertEquals(new Proposition.Always(false), stated(
                "if String.length(String.concat(List.map(c -> \"\", String.characters(b.s))))"
                        + " >= 1 then 1 else 0"));
    }

    /**
     * A string written without the character it was made for is one string for every character:
     * strings joined, that one for each character, hold something where the string holds a
     * character and that one string holds something — whatever kept the characters, where it
     * kept every one.
     */
    @Test
    void stringsWrittenWithoutTheCharacterTheyAreMadeForHoldSomethingWhereBothDo() {
        assertEquals(stated("if String.length(b.s) >= 1 && String.length(b.t) >= 1"
                        + " then 1 else 0"),
                stated("if String.length(String.concat(List.map(c -> b.t,"
                        + " String.characters(b.s)))) >= 1 then 1 else 0"));
        assertEquals(stated("if Bool.not(List.isEmpty(String.words(b.s)))"
                        + " && String.length(b.t) >= 1 then 1 else 0"),
                stated("if String.length(String.concat(List.map(c -> b.t,"
                        + " List.filter(w -> String.length(w) >= 1, String.words(b.s)))))"
                        + " >= 1 then 1 else 0"));
    }

    /**
     * The words of the characters a pattern of one symbol keeps, each other one a space, are some
     * word exactly where the string holds a code point the pattern accepts that is not
     * whitespace: whichever is written, a slug made of them or some character matching, one count
     * of the string's code points in that set.
     */
    @Test
    void wordsOfTheCharactersAPatternKeepsAreTheStringHoldingOneItAccepts() {
        Proposition matching = stated("if List.any(c -> String.matches(\"[a-z0-9]\", c),"
                + " String.characters(b.s)) then 1 else 0");
        assertNull(Proposition.firstStopIn(matching), matching.toString());
        Proposition.Compared compared = assertInstanceOf(Proposition.Compared.class, matching);
        Relation.Affine affine = assertInstanceOf(Relation.Affine.class, compared.relation());
        assertEquals(List.of("#(one of {0030-0039 0061-007A})(b.s)"), affine.form().coefs()
                .keySet().stream().map(Object::toString).toList(), "the one number it is about");
        String kept = "List.map(c -> if String.matches(\"[a-z0-9]\", c) then c else \" \","
                + " String.characters(b.s))";
        assertEquals(matching, stated("if Bool.not(List.isEmpty(String.words(String.concat("
                + kept + ")))) then 1 else 0"));
        assertEquals(matching, stated("if String.length(String.join(\"-\", String.words("
                + "String.concat(" + kept + ")))) >= 1 then 1 else 0"));
        // A space the pattern accepts is still no word.
        assertEquals(matching, stated("if Bool.not(List.isEmpty(String.words(String.concat("
                + "List.map(c -> if String.matches(\"[a-z0-9 ]\", c) then c else \"\","
                + " String.characters(b.s)))))) then 1 else 0"));
        assertEquals(new Proposition.Always(false), stated("if List.any(c -> String.matches("
                + "\"[a-z][0-9]\", c), String.characters(b.s)) then 1 else 0"));
    }

    /**
     * Characters of a string an operation made hold a code point that is not whitespace where
     * that string does, and so where the string the operation was handed does, wherever the
     * operation keeping that stands: before the string is taken into characters, or between
     * putting them back together and cutting that into words.
     */
    @Test
    void charactersOfAStringAnOperationMadeHoldWhatTheOperationKeeps() {
        Proposition words = stated("if String.length(String.join(\"-\", String.words(String.concat("
                + "String.characters(b.s))))) >= 1 then 1 else 0");
        assertNull(Proposition.firstStopIn(words), words.toString());
        for (String made : List.of("String.lowercase", "String.uppercase", "String.trim")) {
            assertEquals(words, stated("if String.length(String.join(\"-\", String.words("
                    + "String.concat(String.characters(" + made + "(b.s)))))) >= 1 then 1 else 0"),
                    made + " before the characters");
            assertEquals(words, stated("if String.length(String.join(\"-\", String.words("
                    + made + "(String.concat(String.characters(b.s)))))) >= 1 then 1 else 0"),
                    made + " after the characters");
        }
    }

    /**
     * Some character of a string an operation made meeting what every code point meets is that
     * string holding something, read as the operation's law says it: a string lowercased or
     * uppercased holds something where the string does, though it is not as long, and one trimmed
     * where the string holds something that is not whitespace.
     */
    @Test
    void someCharacterOfAStringAnOperationMadeIsThatStringHoldingSomething() {
        String anyCharacter = "if List.any(c -> String.matches(\"[^a]\", c)"
                + " || String.matches(\"a\", c), String.characters(%s)) then 1 else 0";
        Proposition ofTheString = stated(anyCharacter.formatted("b.s"));
        assertNull(Proposition.firstStopIn(ofTheString), ofTheString.toString());
        for (String made : List.of("String.lowercase", "String.uppercase")) {
            assertEquals(ofTheString, stated(anyCharacter.formatted(made + "(b.s)")), made);
        }
        Proposition trimmed = stated(anyCharacter.formatted("String.trim(b.s)"));
        assertNull(Proposition.firstStopIn(trimmed), trimmed.toString());
        assertEquals(stated("if Bool.not(String.isEmpty(String.trim(b.s))) then 1 else 0"),
                trimmed);
    }

    /**
     * Characters of a string lowercased are not characters of a string at a position: the case
     * mapping, and the composition after it, can take a letter the pattern accepts into one it
     * does not — {@code J} before a combining caron is {@code ǰ} once lowercased — so which code
     * points of the string make one is not a class of them. It is read as a count of the answer,
     * a number of the string of its own that is worked out by asking the answer, and never as the
     * count the string's own code points have.
     */
    @Test
    void charactersOfAStringLowercasedAreNotReadAsAClassOfTheString() {
        Proposition stated = stated("if List.any(c -> String.matches(\"[a-z0-9]\", c),"
                + " String.characters(String.lowercase(b.s))) then 1 else 0");
        assertNull(Proposition.firstStopIn(stated), stated.toString());
        assertTrue(stated.toString().contains("String.lowercase(b.s)"), stated.toString());
        assertNotEquals(stated, stated("if List.any(c -> String.matches(\"[a-z0-9]\", c),"
                + " String.characters(b.s)) then 1 else 0"));
    }

    /**
     * What a dependency answers for each character is a string for each, one answer apiece: what
     * is stated of it is not stated once of every element, and with no position for the character
     * it is handed it is not read.
     */
    @Test
    void stringsADependencyAnswersForEachCharacterAreNotOneStringForEvery() {
        Proposition stated = stated("if String.length(String.concat(List.map(c -> lookUp(c),"
                + " String.characters(b.s)))) >= 1 then 1 else 0", true);
        assertTrue(Proposition.leavesSomethingUnread(stated), stated.toString());
        // Nor where the character reaches the call through a name the closure gives it.
        Proposition throughAName = stated("if String.length(String.concat(List.map(c -> {\n"
                + "    let d = c\n"
                + "    lookUp(d)\n"
                + "}, String.characters(b.s)))) >= 1 then 1 else 0", true);
        assertTrue(Proposition.leavesSomethingUnread(throughAName), throughAName.toString());
    }

    /**
     * Where what an element was kept by turns on which element it is, some element being kept is
     * not the string holding a character, and with no position for the element it is not read —
     * whether the string made of it is written with the element or without.
     */
    @Test
    void stringsMadeOfTheCharactersAStatementKeptAreNotReadAsTheStringHoldingOne() {
        for (String each : List.of("c -> \" \"", "c -> b.t")) {
            assertInstanceOf(WhyUnread.AtNoPosition.class, Proposition.firstStopIn(stated(
                    "if String.length(String.concat(List.map(" + each + ","
                            + " List.filter(c -> c == \"a\", String.characters(b.s))))) >= 1"
                            + " then 1 else 0")), each);
        }
    }

    /** What the condition of the one fork of a body written {@code body} states. */
    private static Proposition stated(String body) {
        return stated(body, false);
    }

    /** As {@link #stated(String)}, of a behavior that depends on {@code lookUp}, which answers a
     *  string for a string, where {@code callsLookUp}. */
    private static Proposition stated(String body, boolean callsLookUp) {
        Fork fork = fork(body, callsLookUp);
        return Pullback.ofATruth(fork.condition(), fork.reads(), fork.read(), Optional.empty())
                .proposition();
    }

    /** What each rule that reads all of the condition of the one fork of {@code body}, a
     *  comparison, concludes. */
    private static List<Proposition> byEachRule(String body) {
        Fork fork = fork(body, false);
        StatedComparison comparison = BooleanMeaning.asAComparison(fork.condition())
                .orElseThrow(() -> new AssertionError(body + " is a comparison"));
        return Pullback.byEachRule(comparison, fork.reads(), fork.read()).stream()
                .filter(each -> !Proposition.leavesSomethingUnread(each)).toList();
    }

    private record Fork(Core condition, InputReads reads, InputReading read) {}

    /** The condition of the one fork of a body written {@code body}, as the reading meets it. */
    private static Fork fork(String body, boolean callsLookUp) {
        String model = "module demo\n\n" + INPUT + (callsLookUp ? """

                behavior lookUp : (s: String) -> String

                behavior f : (b: Box) -> Int
                    depends on lookUp
                let f (b, lookUp) =
                    %s
                """ : """

                behavior f : (b: Box) -> Int
                let f (b) =
                    %s
                """).formatted(body.indent(4).strip());
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + body);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return new Fork(fork.cond(), reads, inputs.reading(rules));
    }
}
