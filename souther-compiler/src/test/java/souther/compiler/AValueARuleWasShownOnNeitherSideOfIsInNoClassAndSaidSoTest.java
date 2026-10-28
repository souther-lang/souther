package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule shown over some of a position's values draws its classes over those, and a row may write
 * one of the rest. Such a value is in none of the classes, and that is no broken partition: it is
 * a value whose class was not worked out, and the report says so beside the row.
 *
 * <p>The emails end in a lower-case letter or a combining mark, so the domains that are the second
 * piece of one are those strings. One with a combining mark normalization leaves where it is —
 * {@code q} and a combining tilde, which nothing composes — is a value, and it is not held as
 * written, so whether it is the piece of an email is shown neither way.
 */
class AValueARuleWasShownOnNeitherSideOfIsInNoClassAndSaidSoTest {

    private static final String UNPLACED = "a rule there was shown on neither side of it";

    /** A domain past what was shown is placed in no class, and the row says why. */
    @Test
    void aRowWritingAValueLeftOpenIsSaidToBeInNoClassShown() {
        String report = reportFor("q̃");

        assertTrue(report.contains("a row's value at `f/book[*].domain@Some` was read, and "
                + UNPLACED + ", so which class it is in is unknown"), report);
    }

    /** A domain shown on either side is placed in its class, and nothing is said of it. */
    @Test
    void aRowWritingAValueShownOnASideIsPlaced() {
        for (String domain : List.of("c", "Q")) {
            String report = reportFor(domain);
            assertFalse(report.contains(UNPLACED), domain + ": " + report);
        }
    }

    private static String reportFor(String domain) {
        Compilation compilation = Compilation.ofSource("""
                module example.pieces

                data Email = String
                    invariant String.matches("[^@\\\\s]+@[a-z̀-ͯ]+", value)

                data Domain = String
                    invariant String.matches("[^@\\\\s]+", value)

                data Row = { id: String, domain: Domain? }

                data Book = List<Row>

                let hasDomain (text: String, r: Row): Bool =
                    match r.domain with
                        | Some own -> own.value == text
                        | None -> false

                behavior f : (email: Email, book: Book) -> List<Row>

                let f (email, book) =
                    match List.get(1, String.split("@", email.value)) with
                        | Some d -> List.filter(r -> hasDomain(d, r), book.value)
                        | None -> []

                example f
                    | (Email("a@b"), Book([ Row { id = "1", domain = Domain("%s") } ])) -> []
                """.formatted(domain), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
