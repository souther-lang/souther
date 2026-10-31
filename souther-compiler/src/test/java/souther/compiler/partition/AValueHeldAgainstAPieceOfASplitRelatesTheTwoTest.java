package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some piece of a string split at one code point being a value of the input is read as that value
 * being one of the pieces, a relation of the two positions as a value held against what an
 * operation answers of one is ({@link AValueHeldAgainstWhatAnOperationAnswersRelatesTheTwoTest}):
 * whatever the string holds it has a piece, and some value is one of its pieces and some is not,
 * so the statement divides neither.
 *
 * <p>Only a position other than the string's own, and only the value being one of the pieces:
 * the piece being another value says which piece it is. A string held against its own pieces says
 * which strings it holds, which is a division of it that nothing here reads.
 */
class AValueHeldAgainstAPieceOfASplitRelatesTheTwoTest {

    private static List<String> fullReport(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines().toList();
    }

    private static List<String> said(String source) {
        return fullReport(source).stream().map(String::strip)
                .filter(line -> line.startsWith("· not read") || line.startsWith("· no line"))
                .toList();
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
    void aValueHeldAgainstOneOfTheFirstPiecesIsRelatedToTheString() {
        assertEquals(Set.of(relates("3:36", "email"), notShown("3:36", "d")), Set.copyOf(said("""
                module w1
                behavior m : (email: String, d: String) -> Bool
                let m (email, d) = List.any(p -> p == d, List.take(1, String.split("@", email)))
                """)));
    }

    private static String ofTheFork(String at, String position) {
        return "· not read: fork@" + at + " — it is about a value made from this one, and what it"
                + " says about the values here is not worked out, about `" + position + "`";
    }

    @Test
    void severalStatementsAboutTheFirstFewPiecesAreEachRead() {
        assertEquals(Set.of(relates("7:27", "email"), relates("8:27", "email"),
                        notShown("7:27", "d"), notShown("8:27", "d"),
                        ofTheFork("7:5", "d"), ofTheFork("7:5", "email"),
                        ofTheFork("8:5", "d"), ofTheFork("8:5", "email")),
                Set.copyOf(said("""
                        module w1
                        data A
                        data B
                        data C
                        behavior m : (email: String, d: String) -> A | B | C
                        let m (email, d) = {
                            guard List.any(p -> p == d, List.take(2, String.split("@", email))) else A
                            guard List.any(p -> p == d, List.take(1, String.split("@", email))) else B
                            C
                        }
                        """)));
    }

    /**
     * A string with a piece that is the value and one that is not satisfies both of these, so a
     * path that holds both is one some row can take, and the report does not shut it out as a
     * statement and its denial.
     */
    @Test
    void aPieceThatIsTheValueAndAPieceThatIsNotCanBothBeSaid() {
        String source = """
                module probe.quantifier
                data Both
                data Other
                behavior f : (email: String, d: String) -> Both | Other
                let f (email, d) =
                    if List.any(p -> p == d, List.take(2, String.split("@", email)))
                            && List.any(p -> p /= d, List.take(2, String.split("@", email)))
                    then Both
                    else Other
                """;
        assertEquals(Set.of(relates("6:24", "email"), notShown("6:24", "d"),
                        ofTheFork("6:5", "d"), ofTheFork("6:5", "email"),
                        notShown("7:32", "d"), relates("7:32", "email")),
                Set.copyOf(said(source)));
        List<String> report = fullReport(source).stream().map(String::strip).toList();
        boolean bothOnOnePath = false;
        for (int at = 0; at + 1 < report.size(); at++) {
            bothOnOnePath |= report.get(at).equals("· the operation applied at 6:8 answers true")
                    && report.get(at + 1).equals("· the operation applied at 7:16 answers true");
        }
        assertTrue(bothOnOnePath, "both are said of one path: " + report);
    }

    /** None of the pieces taken, the closure is applied to none, and the comparison in it is one
     *  no run makes: it relates nothing and leaves nothing unread. */
    @Test
    void noPieceTakenIsNoRelation() {
        assertEquals(List.of(), said("""
                module w1
                behavior m : (email: String, d: String) -> Bool
                let m (email, d) = List.any(p -> p == d, List.take(0, String.split("@", email)))
                """));
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
