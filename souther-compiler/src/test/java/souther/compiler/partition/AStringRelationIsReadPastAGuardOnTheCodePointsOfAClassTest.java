package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation between two strings is read past a guard on the trimmed length of one of them, where
 * the guard only asks that something is left of it: that is how many of its code points are not
 * whitespace, which is a condition on the strings and no length. The strings the run gets to the
 * relation with are those holding some of the class, and the others are left open, said by how
 * few of the class they hold. A guard on the trimmed length past emptiness is a condition on where
 * the whitespace is, and is still not shown.
 */
class AStringRelationIsReadPastAGuardOnTheCodePointsOfAClassTest {

    private static final String CONTAINS = "String.contains(b.value, a)";

    private static Compilation measured(String aType, String guards, String relation) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Any1 = String invariant String.matches("[\\\\s\\\\S]+", value)
                data Blank = String invariant String.matches("\\\\s+", value)
                data Word = String invariant String.matches("[a-z]+", value)
                data Missed

                behavior f : (a: %s, b: Any1) -> Bool | Missed
                let f (a, b) = {
                    %s
                    %s
                }
                """.formatted(aType, guards, relation), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Compilation guarded(String guard, String relation) {
        return measured("String", guard + " else Missed", relation);
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /** Every reason the report gives about a relation. */
    private static NavigableSet<String> aboutTheRelation(Compilation compilation) {
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = Pattern.compile("\"reason\"\\s*:\\s*\"(relation_[a-z_]+)\"")
                .matcher(json(compilation));
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    /** What the report says is left open for how many code points of a class, as written. */
    private static List<String> openByCodePoints(Compilation compilation) {
        Matcher found = Pattern.compile("\"codePoints\"\\s*:\\s*\\[\\s*\\{([^}]*)\\}")
                .matcher(json(compilation));
        List<String> out = new ArrayList<>();
        while (found.find()) {
            out.add(found.group(1).replaceAll("\\s+", " ").strip());
        }
        return out;
    }

    /** The classes each axis of the behavior is parted into. */
    private static Map<String, List<String>> classes(Compilation compilation) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").axes()
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The reproduction of the issue: both places are read, and the strings of {@code a} short of a
     *  code point that is not whitespace are said to be open. */
    @Test
    void aGuardThatLeavesSomethingOfTheTrimmedStringReadsTheRelation() {
        Compilation compilation = guarded("guard String.length(String.trim(a)) >= 1", CONTAINS);
        NavigableSet<String> reasons = aboutTheRelation(compilation);
        assertTrue(reasons.contains("relation_shown_over_a_region"), reasons::toString);
        assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"), reasons::toString);
        Map<String, List<String>> classes = classes(compilation);
        assertEquals(List.of("a/x can be a string holding b"), classes.get("a"));
        assertEquals(List.of("b/x can be a string inside a"), classes.get("b"));
        assertEquals(List.of("\"class\" : \"not_whitespace\", \"fewerThan\" : 1"),
                openByCodePoints(compilation));
    }

    /** What {@code String.words} leaves empty is what {@code String.trim} does, so the guards are
     *  one reading. */
    @Test
    void theWordsOfAStringAreReadAsItsTrimmedStringIs() {
        Compilation trimmed = guarded("guard String.length(String.trim(a)) >= 1", CONTAINS);
        Compilation words = guarded("guard List.length(String.words(a)) >= 1", CONTAINS);
        assertEquals(aboutTheRelation(trimmed), aboutTheRelation(words));
        assertEquals(classes(trimmed), classes(words));
        assertEquals(openByCodePoints(trimmed), openByCodePoints(words));
    }

    /** The relation does not decide whether the guard is read. */
    @Test
    void theKindOfRelationDoesNotDecideWhetherTheGuardIsRead() {
        for (String relation : List.of(CONTAINS, "String.contains(a, b.value)", "a == b.value",
                "String.startsWith(b.value, a)", "String.endsWith(a, b.value)")) {
            Compilation compilation = guarded("guard String.length(String.trim(a)) >= 1", relation);
            NavigableSet<String> reasons = aboutTheRelation(compilation);
            assertTrue(reasons.contains("relation_shown_over_a_region"), () -> relation + reasons);
            assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"),
                    () -> relation + reasons);
            assertTrue(openByCodePoints(compilation)
                    .contains("\"class\" : \"not_whitespace\", \"fewerThan\" : 1"),
                    () -> relation + openByCodePoints(compilation));
        }
    }

    /** The guard on the length itself is the control, and it is still read as it was: open for
     *  the strings that are short, said by a length and not by a count of a class. */
    @Test
    void aGuardOnTheLengthOfTheStringIsStillSaidByALength() {
        Compilation compilation = guarded("guard String.length(a) >= 1", CONTAINS);
        NavigableSet<String> reasons = aboutTheRelation(compilation);
        assertTrue(reasons.contains("relation_shown_over_a_region"), reasons::toString);
        assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"), reasons::toString);
        assertTrue(json(compilation).contains("\"shorterThan\" : 1"), () -> json(compilation));
        assertEquals(List.of(), openByCodePoints(compilation));
    }

    /** A guard on the string the other is inside is a guard on the strings the other is inside: the
     *  strings of {@code a} that hold {@code b} hold one with a code point that is not whitespace,
     *  and the relation is read as it is with the guard on {@code a}. */
    @Test
    void aGuardOnTheStringTheOtherIsInsideIsReadAsWell() {
        Compilation compilation = guarded("guard String.length(String.trim(b.value)) >= 1", CONTAINS);
        NavigableSet<String> reasons = aboutTheRelation(compilation);
        assertTrue(reasons.contains("relation_shown_over_a_region"), reasons::toString);
        assertFalse(reasons.contains("relation_not_shown_to_reach_every_value"), reasons::toString);
        assertEquals(List.of("a/x can be a string holding b", "a/x is never a string holding b"),
                classes(compilation).get("a"));
    }

    /** A guard that asks for no code point of the class is open at the other end: the strings
     *  that hold some are the ones the run does not get to the relation with. */
    @Test
    void aGuardThatAsksForNoneOfTheClassLeavesTheStringsHoldingSomeOpen() {
        Compilation compilation = guarded("guard String.length(String.trim(a)) < 1", CONTAINS);
        assertTrue(aboutTheRelation(compilation).contains("relation_shown_over_a_region"));
        assertEquals(List.of("\"class\" : \"not_whitespace\", \"moreThan\" : 0"),
                openByCodePoints(compilation));
    }

    /** How long the string is once trimmed is where the whitespace is as well as how much of it
     *  there is: {@code "a  b"} holds two code points that are not whitespace and trims to four.
     *  The count of the class is no reading of it, and nothing is said of the strings. */
    @Test
    void aGuardOnTheTrimmedLengthPastEmptinessIsStillNotShown() {
        for (String guard : List.of("guard String.length(String.trim(a)) >= 2",
                "guard String.length(String.trim(a)) >= 3")) {
            Compilation compilation = guarded(guard, CONTAINS);
            NavigableSet<String> reasons = aboutTheRelation(compilation);
            assertTrue(reasons.contains("relation_not_shown_to_reach_every_value"),
                    () -> guard + reasons);
            assertFalse(reasons.contains("relation_shown_over_a_region"), () -> guard + reasons);
            assertEquals(List.of(), openByCodePoints(compilation), guard);
            assertFalse(classes(compilation).containsKey("a"), () -> guard + classes(compilation));
            assertFalse(classes(compilation).containsKey("b"), () -> guard + classes(compilation));
        }
    }

    /** Two counts of one string in the way are two numbers, and what one says of the other is not
     *  worked out: neither is read as if the other were free. */
    @Test
    void aWayThatStatesTwoCountsOfOneStringIsNotRead() {
        Compilation compilation = measured("String", """
                guard String.length(String.trim(a)) >= 1 else Missed
                    guard String.length(a) >= 2 else Missed""", CONTAINS);
        NavigableSet<String> reasons = aboutTheRelation(compilation);
        assertTrue(reasons.contains("relation_not_shown_to_reach_every_value"), reasons::toString);
        assertFalse(reasons.contains("relation_shown_over_a_region"), reasons::toString);
    }

    /**
     * Where every string of the place holds a code point that is not whitespace the guard keeps
     * none of them from the relation, and nothing is open for it. Where none does, the run gets
     * to the relation with no string of the place, which every string being open says and which
     * no class of the place is drawn over.
     */
    @Test
    void aRegionNoStringIsOpenInIsToldFromOneEveryStringIsOpenIn() {
        Compilation word = measured("Word",
                "guard String.length(String.trim(a.value)) >= 1 else Missed", "a.value == b.value");
        assertEquals(List.of(), openByCodePoints(word));
        assertEquals(List.of("b/x can be a", "b/x is never a"), classes(word).get("b"));

        Compilation blank = measured("Blank",
                "guard String.length(String.trim(a.value)) >= 1 else Missed", "a.value == b.value");
        assertEquals(List.of("\"class\" : \"not_whitespace\", \"fewerThan\" : 1"),
                openByCodePoints(blank));
        assertFalse(classes(blank).containsKey("a"), () -> classes(blank).toString());
        assertFalse(classes(blank).containsKey("b"), () -> classes(blank).toString());
    }

    /** The strings shown to be none of the other side's are those that cannot be: the strings of
     *  {@code b} that hold nothing but whitespace are never {@code a}, which holds a code point
     *  that is not. */
    @Test
    void aStringHoldingOnlyWhitespaceIsShownNeverToBeTheOneTheGuardKeepsToOtherStrings() {
        Compilation compilation = guarded("guard String.length(String.trim(a)) >= 1",
                "a == b.value");
        assertEquals(List.of("b/x can be a", "b/x is never a"), classes(compilation).get("b"));
        assertEquals(List.of("a/x can be b"), classes(compilation).get("a"));
    }
}
