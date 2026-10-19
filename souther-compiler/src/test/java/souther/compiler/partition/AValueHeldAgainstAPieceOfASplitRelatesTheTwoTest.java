package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value of the input held against a piece of a string split at one code point is read as a
 * relation of the two positions, as it is against what an operation answers of one
 * ({@link AValueHeldAgainstWhatAnOperationAnswersRelatesTheTwoTest}): whatever the string holds,
 * some value is one of its pieces and some is not, so the comparison divides neither.
 *
 * <p>Only a position other than the string's own. A string held against its own pieces says which
 * strings it holds, which is a division of it that nothing here reads.
 */
class AValueHeldAgainstAPieceOfASplitRelatesTheTwoTest {

    private static List<String> said(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .lines().map(String::strip).filter(line -> line.startsWith("· not read")
                        || line.startsWith("· no line")).toList();
    }

    private static String relates(String at, String position) {
        return "· no line: comparison@" + at + " — it relates the value here to another value rather"
                + " than dividing the values here, about `" + position + "`";
    }

    private static String notShown(String at, String position) {
        return "· not read: comparison@" + at + " — what it states was read, and it relates the"
                + " value here to another value not shown to reach every value here, so which values"
                + " here settle it on their own is not worked out, about `" + position + "`";
    }

    @Test
    void aValueHeldAgainstAPieceIsRelatedToTheString() {
        assertEquals(Set.of(relates("3:36", "email"), notShown("3:36", "d")), Set.copyOf(said("""
                module w1
                behavior m : (email: String, d: String) -> Bool
                let m (email, d) = List.any(p -> p == d, String.split("@", email))
                """)));
    }

    @Test
    void theStringHeldAgainstItsOwnPiecesIsNotRead() {
        assertEquals(List.of("· not read: comparison@3:36 — written in a form this compiler does not"
                + " read, about `email`"), said("""
                module w1
                behavior m : (email: String, d: String) -> Bool
                let m (email, d) = List.any(p -> p == email, String.split("@", email))
                """));
    }

    @Test
    void aPieceWrappedInANewtypeIsTheSamePiece() {
        assertEquals(Set.of(notShown("6:36", "d"), notShown("6:36", "email")), Set.copyOf(said("""
                module w1
                data Domain = String
                    invariant String.length(value) >= 3
                behavior m : (email: String, d: Domain) -> Bool
                    constructs Domain
                let m (email, d) = List.any(p -> p == d, List.map(x -> Domain(x), String.split("@", email)))
                """)));
    }
}
