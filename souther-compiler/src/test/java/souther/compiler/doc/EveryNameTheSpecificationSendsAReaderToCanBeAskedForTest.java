package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A cross-reference is the specification telling a reader where to go. `souther doc` is how a
 * reader gets there without the document in front of them, so a name the text sends them to and a
 * name the command refuses is the document promising something the tool does not keep.
 *
 * <p>The names are read out of the specification's own text rather than listed from the resolver.
 * Asking the resolver which names it knows and then asking it about those names would pass whatever
 * the resolver did — the point is that the side that writes the references and the side that
 * answers them agree.
 */
class EveryNameTheSpecificationSendsAReaderToCanBeAskedForTest {

    /** An AsciiDoc cross-reference: {@code <<anchor>>} or {@code <<anchor,the words shown>>}. */
    private static final Pattern XREF = Pattern.compile("<<([^,>]+)[^>]*>>");

    @Test
    void everyCrossReferenceInTheSpecificationResolvesToASection() {
        SpecDocument spec = SpecDocument.bundled();
        Set<String> unresolved = new TreeSet<>();
        Matcher m = XREF.matcher(text());
        while (m.find()) {
            if (spec.section(m.group(1)) == null) {
                unresolved.add(m.group(1));
            }
        }

        assertEquals(Set.of(), unresolved,
                "the specification sends a reader to these and `souther doc` has no answer for them");
    }

    @Test
    void aReferenceIsFoundAtAllSoTheScanIsNotLookingAtAnEmptyDocument() {
        assertFalse(XREF.matcher(text()).results().findAny().isEmpty(),
                "found no cross-reference at all — the scan missed the document");
    }

    @Test
    void aHeadingCarryingSeveralAnchorsIsAskedForByEachOfThem() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#first]
                [#second]
                == One heading, two names

                What both names answer with.

                [#other]
                == Another

                Something else.
                """);

        SpecDocument.Section section = spec.section("first");

        assertNotNull(section);
        assertSame(section, spec.section("second"), "the second name answers with the same section");
        assertEquals("first", section.anchor(), "and the section is listed under the first written");
        assertEquals(2, spec.sections().size(), "a further name is not a section of its own");
        assertEquals("What both names answer with.", section.body(),
                "the body starts after the heading, not inside the anchors");
    }

    @Test
    void anAnchorOnAParagraphIsAnsweredWithTheSectionItStandsIn() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#surrounding]
                == The section it stands in

                Opening words.

                [#a-rule]
                A rule finer than a section.

                [#later]
                == A later section

                Something else.
                """);

        SpecDocument.Section section = spec.section("a-rule");

        assertNotNull(section, "a name the document points at is a name a reader can ask for");
        assertSame(spec.section("surrounding"), section);
        assertEquals(2, spec.sections().size(), "and it is not a section of its own");
    }

    @Test
    void theBodyOfASectionStopsBeforeTheAnchorsOfTheNextOne() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#one]
                == One

                The body of one.

                [#two-first]
                [#two-second]
                == Two

                The body of two.
                """);

        assertEquals("The body of one.", spec.section("one").body());
    }

    @Test
    void aNameAnsweredWithTheSectionAroundItSaysThatIsWhatHappened() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();

        int code = DocCommand.run(new String[]{"union-member"},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        String said = err.toString(StandardCharsets.UTF_8);

        assertEquals(0, code, said);
        assertTrue(said.contains("`union-member` is written in"),
                "the reader is told which section answered: " + said);
        assertFalse(out.toString(StandardCharsets.UTF_8).isBlank(), "and the section itself is printed");
    }

    private static String text() {
        try (InputStream in = SpecDocument.class.getResourceAsStream("/META-INF/souther/specification.adoc")) {
            assertNotNull(in, "the specification travels in the jar");
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
