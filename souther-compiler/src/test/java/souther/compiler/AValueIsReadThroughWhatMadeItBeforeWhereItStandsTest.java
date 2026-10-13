package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard over a value the body made is read through what made it, and is measured as the guard
 * written over what that was made of.
 *
 * <p>Two models, each the way an author wrote it. A text made of the words of a lowercased title,
 * or of the characters of one put back together, holds something where the title holds a code
 * point that is not whitespace; and every item of a
 * list a helper chooses by whether the cart is open meeting a statement is the cart being closed,
 * or every item of it meeting it. Each is asked of the report a person reads, which is where a
 * rule this could not read came out.
 */
class AValueIsReadThroughWhatMadeItBeforeWhereItStandsTest {

    private static String measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> notRead(String report) {
        return report.lines().filter(line -> line.contains("not read")
                || line.contains("not accounted for")).toList();
    }

    @Test
    void aTextMadeOfTheWordsOfATitleIsMeasuredOnTheTitle() {
        String report = measured("""
                module p
                behavior f : (t: String) -> Bool
                let f (t) = String.length(String.join("-", String.words(String.lowercase(t)))) >= 1
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(report.contains("read as f/#(not whitespace)(t): = 0"), report);
        assertTrue(report.contains("read as f/#(not whitespace)(t): = 1"), report);
    }

    @Test
    void aTextMadeOfTheCharactersOfALowercasedTitleIsMeasuredOnTheTitle() {
        String report = measured("""
                module p
                behavior f : (t: String) -> Int
                let f (t) =
                    if String.length(t |> String.lowercase |> String.characters |> String.concat
                        |> String.words |> String.join("-")) >= 1 then 1 else 0
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(report.contains("read as f/#(not whitespace)(t): = 0"), report);
        assertTrue(report.contains("read as f/#(not whitespace)(t): = 1"), report);
    }

    @Test
    void aTextMadeOfOneStringForEachCharacterOfATitleIsMeasuredOnTheTitle() {
        String report = measured("""
                module p
                let spaced (title: String): String =
                    title
                        |> String.characters
                        |> List.map(c -> if String.matches("[a-z0-9]", c) then c else " ")
                        |> String.concat
                behavior f : (t: String) -> Int
                let f (t) = {
                    let text = spaced(t)
                    if String.length(text) >= 1 then 1 else 0
                }
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(report.contains("read as f/String.length(t): = 0"), report);
        assertTrue(report.contains("read as f/String.length(t): = 1"), report);
    }

    @Test
    void aSlugOfTheCharactersAPatternKeepsIsMeasuredOnTheCodePointsOfTheTitleItAccepts() {
        String report = measured("""
                module p
                let slugText (title: String): String =
                    title
                        |> String.characters
                        |> List.map(c -> if String.matches("[a-zA-Z0-9]", c) then c else " ")
                        |> String.concat
                        |> String.words
                        |> String.join("-")
                        |> String.lowercase
                behavior f : (t: String) -> Int
                let f (t) = {
                    let text = slugText(t)
                    if String.length(text) >= 1 then 1 else 0
                }
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(report.contains(
                "read as f/#(one of {0030-0039 0041-005A 0061-007A})(t): = 0"), report);
        assertTrue(report.contains(
                "read as f/#(one of {0030-0039 0041-005A 0061-007A})(t): = 1"), report);
    }

    @Test
    void aQuantifierOverAListAHelperChoosesIsMeasuredOnTheListsItChoosesFrom() {
        String report = measured("""
                module p
                data LI = { q: Int }
                data Cart = { open: Bool, items: List<LI> }
                data Empty = { n: Int }
                let act (c: Cart) = if c.open then c.items else []
                behavior f : (c: Cart) -> Int | Empty
                let f (c) = { guard List.all(i -> i.q >= 1, act(c)) else Empty { n = 0 }
                 1 }
                """);
        assertEquals(List.of(), notRead(report));
        assertTrue(report.contains("read as f/c.items[*].q: = 1"), report);
        assertTrue(report.contains("read as f/c.items[*].q: = 0"), report);
        assertTrue(report.contains("partition   axes 2"), report);
    }
}
