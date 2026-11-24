package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

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
 * relation with are those holding some of the class, and the others are the guard's: the relation
 * is not asked of them, and leaves none of them open. A guard on the trimmed length past emptiness
 * is a condition on where the whitespace is, and is still not shown.
 */
class AStringRelationIsReadPastAGuardOnTheCodePointsOfAClassTest {

    private static final String CONTAINS = "String.contains(b.value, a)";

    private static Compilation measured(String aType, String guards, String relation) {
        return ACompiledModel.measured("""
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
                """.formatted(aType, guards, relation), Adequacy.Asked.fullReport());
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

    /** Whether the report says some value is left open. */
    private static boolean leavesSomeOpen(Compilation compilation) {
        return json(compilation).contains("\"leftOpen\"");
    }

    /** The classes each axis of the behavior is parted into. */
    private static Map<String, List<String>> classes(Compilation compilation) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").axes()
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The reproduction of the issue: both places are read, and the strings of {@code a} short of a
     *  code point that is not whitespace are the guard's, and none is left open. Every {@code a}
     *  the run gets to the relation with is inside some {@code b}, and every {@code b} is inside an
     *  {@code a} it makes with a letter after it and outside another, so the relation tells none of
     *  them apart. */
    @Test
    void aGuardThatLeavesSomethingOfTheTrimmedStringReadsTheRelation() {
        Compilation compilation = guarded("guard String.length(String.trim(a)) >= 1", CONTAINS);
        assertEquals(new TreeSet<String>(), aboutTheRelation(compilation));
        Map<String, List<String>> classes = classes(compilation);
        assertFalse(classes.containsKey("a"), classes::toString);
        assertTrue(!classes.containsKey("b") || classes.get("b").size() <= 1, classes::toString);
        assertFalse(leavesSomeOpen(compilation), () -> json(compilation));
    }

    /** What {@code String.words} leaves empty is what {@code String.trim} does, so the guards are
     *  one reading. */
    @Test
    void theWordsOfAStringAreReadAsItsTrimmedStringIs() {
        Compilation trimmed = guarded("guard String.length(String.trim(a)) >= 1", CONTAINS);
        Compilation words = guarded("guard List.length(String.words(a)) >= 1", CONTAINS);
        assertEquals(aboutTheRelation(trimmed), aboutTheRelation(words));
        assertEquals(classes(trimmed), classes(words));
        assertEquals(leavesSomeOpen(trimmed), leavesSomeOpen(words));
    }

    /** The relation does not decide whether the guard is read. */
    @Test
    void theKindOfRelationDoesNotDecideWhetherTheGuardIsRead() {
        for (String relation : List.of(CONTAINS, "String.contains(a, b.value)", "a == b.value",
                "String.startsWith(b.value, a)", "String.endsWith(a, b.value)")) {
            Compilation compilation = guarded("guard String.length(String.trim(a)) >= 1", relation);
            NavigableSet<String> reasons = aboutTheRelation(compilation);
            assertEquals(new TreeSet<String>(), reasons, relation);
            assertFalse(leavesSomeOpen(compilation), relation);
        }
    }

    /** The guard on the length itself is the control, and it is read the same way: the strings
     *  that are short are the guard's, said by no length and no count of a class. The string
     *  looked in is any string, and each string is a partner of itself, so none of its strings is
     *  open. */
    @Test
    void aGuardOnTheLengthOfTheStringIsReadAsTheGuardOnTheCountIs() {
        Compilation compilation = guarded("guard String.length(a) >= 1", CONTAINS);
        assertFalse(aboutTheRelation(compilation).contains("relation_shown_over_a_region"),
                () -> aboutTheRelation(compilation).toString());
        assertFalse(leavesSomeOpen(compilation), () -> json(compilation));
    }

    /** A guard on the string the other is inside is a guard on the strings the other is inside: the
     *  strings of {@code a} that hold {@code b} hold one with a code point that is not whitespace,
     *  and the relation is read as it is with the guard on {@code a}. */
    @Test
    void aGuardOnTheStringTheOtherIsInsideIsReadAsWell() {
        Compilation compilation = guarded("guard String.length(String.trim(b.value)) >= 1", CONTAINS);
        assertEquals(new TreeSet<String>(), aboutTheRelation(compilation));
        assertFalse(leavesSomeOpen(compilation), () -> json(compilation));
        assertEquals(List.of("a: x can be a string holding b", "a: x is never a string holding b"),
                classes(compilation).get("a"));
    }

    /** A guard that asks for no code point of the class keeps the other end from the relation: the
     *  strings that hold some are the guard's, and are left open for nothing. */
    @Test
    void aGuardThatAsksForNoneOfTheClassLeavesTheStringsHoldingSomeToTheGuard() {
        Compilation compilation = guarded("guard String.length(String.trim(a)) < 1", CONTAINS);
        assertFalse(aboutTheRelation(compilation).contains("relation_shown_over_a_region"));
        assertFalse(leavesSomeOpen(compilation), () -> json(compilation));
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
            assertFalse(leavesSomeOpen(compilation), guard);
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
     * none of them from the relation, and the classes are drawn over all of them. Where none does,
     * the run gets to the relation with no string of the place, which no class of the place is
     * drawn over, and none is left open.
     */
    @Test
    void aPlaceTheRunGetsToTheRelationWithNoStringOfHasNoClassForIt() {
        Compilation word = measured("Word",
                "guard String.length(String.trim(a.value)) >= 1 else Missed", "a.value == b.value");
        assertFalse(leavesSomeOpen(word), () -> json(word));
        assertEquals(List.of("b: x can be a", "b: x is never a"), classes(word).get("b"));

        Compilation blank = measured("Blank",
                "guard String.length(String.trim(a.value)) >= 1 else Missed", "a.value == b.value");
        assertFalse(leavesSomeOpen(blank), () -> json(blank));
        assertFalse(classes(blank).containsKey("a"), () -> classes(blank).toString());
        assertFalse(classes(blank).containsKey("b"), () -> classes(blank).toString());
    }

    /** The strings shown to be none of the other side's are those that cannot be: the strings of
     *  {@code b} that hold nothing but whitespace are never {@code a}, which holds a code point
     *  that is not. Every {@code a} the run gets to the relation with can be some {@code b}, so
     *  the relation tells none of them apart. */
    @Test
    void aStringHoldingOnlyWhitespaceIsShownNeverToBeTheOneTheGuardKeepsToOtherStrings() {
        Compilation compilation = guarded("guard String.length(String.trim(a)) >= 1",
                "a == b.value");
        assertEquals(List.of("b: x can be a", "b: x is never a"), classes(compilation).get("b"));
        assertFalse(classes(compilation).containsKey("a"), () -> classes(compilation).toString());
    }
}
