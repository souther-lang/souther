package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * `souther doc` is how an agent or a person reads the language specification without the repo:
 * no argument lists the sections, an anchor prints one, --search finds them by what they say.
 */
class TheDocCommandAnswersFromTheBundledSpecTest {

    private record Answer(int code, String out, String err) {}

    private Answer run(String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = DocCommand.run(args,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        return new Answer(code, out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void withNoArgumentEverySectionIsListedAsAnchorAndTitle() {
        Answer answer = run();

        assertEquals(0, answer.code());
        assertTrue(answer.out().lines().findFirst().orElseThrow().matches("purpose\t.*Purpose"),
                "the first line names the first section: " + answer.out().lines().findFirst().orElseThrow());
        assertTrue(answer.out().lines().count() > 100, "every section is listed");
    }

    @Test
    void anAnchorPrintsThatSectionsTitleAndBody() {
        Answer answer = run("purpose");

        assertEquals(0, answer.code());
        assertTrue(answer.out().contains("Purpose"));
        assertTrue(answer.out().contains("JVM-targeted language"));
    }

    @Test
    void searchListsTheSectionsThatSayTheTerm() {
        Answer answer = run("--search", "single-value newtype");

        assertEquals(0, answer.code());
        assertTrue(answer.out().lines().anyMatch(l -> l.startsWith("newtype-comparison\t")),
                "a term nobody is named after is answered with the sections that say it:\n"
                        + answer.out());
    }

    @Test
    void anUnknownAnchorSaysSoAndSuggestsNearNames() {
        Answer answer = run("newtypes");

        assertEquals(2, answer.code());
        assertTrue(answer.err().contains("no section `newtypes`"), answer.err());
        assertTrue(answer.err().contains("newtype"), "a near anchor is suggested: " + answer.err());
    }
}
