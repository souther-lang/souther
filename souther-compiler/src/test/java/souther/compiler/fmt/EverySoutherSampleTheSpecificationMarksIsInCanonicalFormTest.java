package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.doc.SpecDocument;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sample the specification marks as Souther is a complete fragment, and it is written in the form
 * {@code souther fmt} writes.
 *
 * <p>The specification is what a first-time author copies, so a sample that the formatter then
 * rewrites teaches a form the tool rejects. Holding the two against each other makes the document
 * the formatter's corpus: the published statement of the canonical form and the executable one stop
 * being two things that can drift apart with nothing to say which of them moved.
 *
 * <p>Membership is what the document declares, not what happens to parse. A block is checked
 * because it is written {@code [,souther]} — an author saying this is Souther and not pseudo-code —
 * and a block written {@code [,text]} is a fragment, a spec-DSL line, or a form being quoted rather
 * than offered. Taking every block that parses instead would make the parser decide what is
 * checked, and a parser that grew would pull samples in without anyone marking them.
 *
 * <p>So the way to bring a sample under this is to mark it, and marking it is a claim about the
 * sample that this refutes if it is false. Samples still written {@code [,text]} are not covered
 * and are not asserted to be anything.
 */
class EverySoutherSampleTheSpecificationMarksIsInCanonicalFormTest {

    /** The attribute line a listing carries. A language of {@code souther} is the mark. */
    private static final Pattern SOUTHER_BLOCK =
            Pattern.compile("^\\[(?:[a-z]*),\\s*souther\\s*(?:,.*)?]$");

    private static final Pattern DELIMITER = Pattern.compile("^----$");

    @Test
    void everyMarkedSampleParses() {
        List<String> broken = new ArrayList<>();
        for (Sample sample : samples()) {
            List<?> errors = CstParser.parse(sample.text()).errors();
            if (!errors.isEmpty()) {
                broken.add("specification.adoc:" + sample.line() + " " + errors);
            }
        }
        assertEquals(List.of(), broken,
                broken.size() + " samples are marked `[,souther]` and are not complete Souther;"
                        + " a fragment is written `[,text]`");
    }

    @Test
    void everyMarkedSampleIsWrittenAsTheFormatterWritesIt() {
        List<String> differ = new ArrayList<>();
        for (Sample sample : samples()) {
            if (!CstParser.parse(sample.text()).errors().isEmpty()) {
                continue;                 // said by the test above; nothing to format
            }
            if (!sample.text().equals(Formatter.format(sample.text()))) {
                differ.add("specification.adoc:" + sample.line());
            }
        }
        assertEquals(List.of(), differ,
                differ.size() + " marked samples are not in canonical form. A sample teaches the"
                        + " form a reader copies, so either write it as `souther fmt` does or take"
                        + " the `[,souther]` mark off it.");
    }

    /** A run that found no marked sample would pass both assertions above having asked nothing. */
    @Test
    void thereAreMarkedSamples() {
        assertTrue(samples().size() >= 20,
                "only " + samples().size() + " samples are marked; the sweep found nothing");
    }

    /** A marked sample: its text, and the line its first line is on. */
    private record Sample(String text, int line) {}

    private static List<Sample> samples() {
        List<String> lines = List.of(read().split("\n", -1));
        List<Sample> out = new ArrayList<>();
        for (int i = 0; i < lines.size() - 1; i++) {
            if (!SOUTHER_BLOCK.matcher(lines.get(i)).matches()
                    || !DELIMITER.matcher(lines.get(i + 1)).matches()) {
                continue;
            }
            int from = i + 2;
            int to = from;
            while (to < lines.size() && !DELIMITER.matcher(lines.get(to)).matches()) {
                to++;
            }
            out.add(new Sample(String.join("\n", lines.subList(from, to)) + "\n", from + 1));
            i = to;
        }
        return out;
    }

    private static String read() {
        // The specification the build bundled, which is the one `souther doc` answers from. Read
        // from the tree instead, this would be checking a document the shipped compiler may not
        // have.
        String resource = "/META-INF/souther/specification.adoc";
        try (InputStream in = SpecDocument.class.getResourceAsStream(resource)) {
            if (in == null) {
                throw new IllegalStateException(resource + " is not on the class path");
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
