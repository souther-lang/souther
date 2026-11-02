package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The pieces of a string that reach a relation are the ones the way holds to a language, and the
 * strings of each side are told apart as that parts them.
 *
 * <p>An attempt to build a value of a type whose rule is a pattern takes its arm for the pieces
 * that meet the pattern. A comparison in that arm is reached with those pieces only, so a string
 * of the other side is the partner's where it is a piece in that language, and is none of them
 * where it is not. A string with none of that language's pieces is one no run gets to the
 * comparison with a piece of: it is the partner's neither way, and the equality is not false at it
 * but not asked.
 */
class ThePiecesThatReachARelationAreHeldToTheLanguageTheWayHoldsThemToTest {

    private static final String MODEL = """
            module probe.c

            data Letters = String
                invariant String.matches("[a-z]+", value)

            data Word = String
                invariant String.matches("[a-z0-9]+", value)

            data Yes
            data No

            behavior f : (s: String, r: Word) -> Yes | No
                constructs Letters

            let f (s, r) =
                if List.length(List.flatMap(d -> if Letters(d) as n then (if n.value == r.value then [ n ] else [ ]) else [ ], String.split("@", s))) >= 1
                then Yes else No

            example f
                | "hit" : ("x@abc", Word("abc")) -> Yes
                | "miss" : ("x@abc", Word("ab")) -> No
                | "none" : ("x@A1", Word("a")) -> No
            """;

    /** The classes of each axis the model divides, by the path of the position. */
    private static Map<String, Set<String>> classesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(java.util.List.of(), compilation.errors(), "the model under test compiles");
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        Map<String, Set<String>> out = new TreeMap<>();
        all.get("f").axes().forEach(axis -> out.put(axis.path(), Set.copyOf(axis.classes())));
        return out;
    }

    /**
     * The partner holds every piece the arm is reached with, so a string with such a piece can be
     * it, and a string with none is in no class of its own: the equality is not false at it, it
     * is not asked.
     */
    @Test
    void aStringWithNoPieceInTheLanguageIsInNoClassOfItsOwn() {
        Map<String, Set<String>> classes = classesOf(MODEL);
        assertEquals(Set.of("s: x can be r"), classes.get("s"), classes::toString);
        assertEquals(Set.of("r: x can be a piece from 0 of s",
                "r: x is never a piece from 0 of s"), classes.get("r"), classes::toString);
    }

    /**
     * The partner holds fewer strings than the language, so a string with a piece in the language
     * that is none of the partner's is one the equality is false at: the class the strings with
     * none of the language's pieces are not in.
     */
    @Test
    void aStringWithAPieceInTheLanguageThatIsNoneOfThePartnersIsFalseThere() {
        Map<String, Set<String>> classes = classesOf(MODEL.replace("[a-z0-9]+", "[a-c]+"));
        assertEquals(Set.of("s: x can be r", "s: x is never r"), classes.get("s"),
                classes::toString);
    }

    /**
     * The pieces are those of the converted string, and the classes are told apart as they are
     * with the string as it stands: the strings the conversion is exactly a map on are parted by
     * the language, and the rest are shown neither way.
     */
    @Test
    void theStringsOfAConvertedStringAreToldApartAsTheStringsAsTheyStandAre() {
        Map<String, Set<String>> classes = classesOf(MODEL.replace("String.split(\"@\", s)",
                "String.split(\"@\", String.lowercase(s))"));
        assertEquals(Set.of("s: x can be r"), classes.get("s"), classes::toString);
        assertEquals(Set.of("r: x can be a piece from 0 of String.lowercase(s)",
                "r: x is never a piece from 0 of String.lowercase(s)"), classes.get("r"),
                classes::toString);
    }

    private static final String LOWERED = MODEL.replace("String.split(\"@\", s)",
            "String.split(\"@\", String.lowercase(s))");

    /** The partner holds fewer strings than the language, as it does for the string as it stands. */
    @Test
    void aConvertedStringWithAPieceInTheLanguageThatIsNoneOfThePartnersIsFalseThere() {
        Map<String, Set<String>> classes = classesOf(LOWERED.replace("[a-z0-9]+", "[a-c]+"));
        assertEquals(Set.of("s: x can be r", "s: x is never r"), classes.get("s"),
                classes::toString);
    }

    /**
     * The pieces of the string as it stands are not the pieces the arm is reached with: those are
     * the converted string's. A string with a piece in the language as it stands, whose converted
     * string has none, is a string no run gets to the relation with a piece of, and the equality
     * is not false at it.
     */
    @Test
    void aStringWhosePiecesAreInTheLanguageOnlyBeforeTheConversionIsNotOneTheEqualityIsFalseAt() {
        String model = LOWERED.replace("matches(\"[a-z]+\"", "matches(\"[A-Z]+\"")
                .replace("[a-z0-9]+", "[a-c]+");
        assertTrue(model.contains("[A-Z]+"), model);
        String source = model.substring(0, model.indexOf("example f")) + """
                example f
                    | "a" : ("x@abc", Word("abc")) -> No
                    | "b" : ("x@ABC", Word("ab")) -> No
                """;
        Set<String> sClasses = classesOf(source).getOrDefault("s", Set.of());
        assertTrue(!sClasses.contains("s: x is never r"), sClasses::toString);
    }

    /**
     * What the conversion makes of a string is not shown for every string, and the report says
     * so of the string the pieces are of: the classes are drawn over the strings it is shown for.
     */
    @Test
    void theImageOfAConversionNotShownIsSaidOfTheStringTheClassesAreOver() {
        String report = reportOf(LOWERED);
        assertTrue(report.lines().anyMatch(line -> line.contains(
                "which class this rule puts some values in at s")
                && line.contains("the image of String.lowercase not shown")), report);
    }

    /**
     * A statement about the pieces of one conversion of a string is no statement about the pieces
     * of another: the pieces of the uppercase string a comparison is over are not held to the
     * language the pieces of the lowercase string are, and nothing is shown of them.
     */
    @Test
    void aStatementAboutLowercasePiecesIsNotAppliedToUppercasePieces() {
        String model = MODEL.substring(0, MODEL.indexOf("example f")) + """
                example f
                    | "a" : ("x@abc", Word("abc")) -> No
                    | "b" : ("x@A1", Word("a")) -> No
                """;
        String report = reportOf(model.replace(
                "if n.value == r.value then [ n ] else [ ]",
                "if List.any(u -> u == r.value, String.split(\"@\", String.uppercase(s)))"
                        + " then [ n ] else [ ]").replace("String.split(\"@\", s))) >= 1",
                "String.split(\"@\", String.lowercase(s)))) >= 1"));
        assertTrue(report.contains("relates the value here to another value not shown to reach"
                + " every value here"), report);
        assertTrue(!report.contains("its classes hold the values it was shown over"), report);
    }

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(java.util.List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The window the pieces were taken in is the window the language is held to. */
    @Test
    void theWindowOfThePiecesIsKept() {
        Map<String, Set<String>> classes = classesOf(MODEL.replace("String.split(\"@\", s)",
                "List.drop(1, String.split(\"@\", s))"));
        assertEquals(Set.of("r: x can be a piece from 1 of s",
                "r: x is never a piece from 1 of s"), classes.get("r"), classes::toString);
        assertEquals(Set.of("s: x can be r"), classes.get("s"), classes::toString);
    }
}
