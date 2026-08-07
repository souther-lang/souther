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
import static org.junit.jupiter.api.Assertions.assertThrows;
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

    /** The delimiter of a block AsciiDoc takes as it stands: listing, literal, passthrough, and the
     *  comment block. A macro is not expanded inside any of them, so nothing there is a reference.
     *  Four or more of the character, closed by the line that repeats it exactly. */
    private static final Pattern OPAQUE_DELIMITER = Pattern.compile("^([-.+/])\\1{3,}$");

    @Test
    void everyCrossReferenceInTheSpecificationResolvesToASection() {
        SpecDocument spec = SpecDocument.bundled();
        Set<String> unresolved = new TreeSet<>();
        for (String reference : referencesIn(text())) {
            if (spec.section(reference) == null) {
                unresolved.add(reference);
            }
        }

        assertEquals(Set.of(), unresolved,
                "the specification sends a reader to these and `souther doc` has no answer for them");
    }

    @Test
    void aReferenceIsFoundAtAllSoTheScanIsNotLookingAtAnEmptyDocument() {
        assertFalse(referencesIn(text()).isEmpty(),
                "found no cross-reference at all — the scan missed the document");
    }

    @Test
    void whatAListingOrACommentWritesIsNotAReference() {
        assertEquals(Set.of("real"), referencesIn("""
                A paragraph pointing at <<real>>.

                [,text]
                ----
                A listing writing <<listed>>, which AsciiDoc leaves as it stands.
                ----

                // A line comment writing <<commented>>.

                ////
                A comment block writing <<blocked>>.
                ////
                """));
    }

    /** The names the document sends a reader to, where AsciiDoc expands a macro at all. */
    private static Set<String> referencesIn(String adoc) {
        Set<String> found = new TreeSet<>();
        String opaque = null;
        for (String line : adoc.split("\n", -1)) {
            String delimiter = line.strip();
            if (opaque != null) {
                if (delimiter.equals(opaque)) {
                    opaque = null;
                }
                continue;
            }
            if (OPAQUE_DELIMITER.matcher(delimiter).matches()) {
                opaque = delimiter;
                continue;
            }
            if (line.startsWith("//")) {
                continue;
            }
            Matcher m = XREF.matcher(line);
            while (m.find()) {
                found.add(m.group(1));
            }
        }
        return found;
    }

    @Test
    void aHeadingIsAlsoAskedForByTheNamesWrittenBesideItsAnchor() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#first]
                [also-named="second,third"]
                == One heading, three names

                What all three names answer with.

                [#other]
                == Another

                Something else.
                """);

        SpecDocument.Section section = spec.section("first");

        assertNotNull(section);
        assertSame(section, spec.section("second"), "a further name answers with the same section");
        assertSame(section, spec.section("third"));
        assertEquals("first", section.anchor(), "and the section is listed under its anchor");
        assertEquals(2, spec.sections().size(), "a further name is not a section of its own");
        assertEquals("What all three names answer with.", section.body(),
                "the body starts after the heading, not inside the attributes");
    }

    /**
     * AsciiDoc gives a heading exactly one ID: written twice, the last is the heading's ID and no
     * target is registered for the first. Reading the first here would be this document knowing a
     * heading by a name no renderer — and no deep link into the published specification — knows it
     * by, which is the divergence a name added for `souther doc` has to stay out of.
     */
    @Test
    void aHeadingWrittenWithTwoAnchorsIsRefusedRatherThanReadOneWayHereAndAnotherByAsciiDoc() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> SpecDocument.of("""
                        = A specification

                        [#first]
                        [#second]
                        == One heading under two identities

                        Something.
                        """));

        assertTrue(refused.getMessage().contains("first") && refused.getMessage().contains("second"),
                "the refusal names both of them: " + refused.getMessage());
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
    void theBodyOfASectionStopsBeforeTheAttributesOfTheNextOne() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#one]
                == One

                The body of one.

                [#two]
                [also-named="two-again"]
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

    /**
     * A near miss is suggested from what a reader could have asked for, which is every name that
     * resolves. Suggesting from the sections alone would answer `no section` to a typo on a name
     * that does resolve, and say nothing about the name itself — the same shape of gap as answering
     * nothing for the name in the first place, one keystroke further out.
     */
    @Test
    void aNearMissOnANameThatIsNotASectionOfItsOwnIsSuggestedToo() {
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        PrintStream discard = new PrintStream(ByteArrayOutputStream.nullOutputStream(), true,
                StandardCharsets.UTF_8);

        DocCommand.run(new String[]{"e2015x"}, discard,
                new PrintStream(err, true, StandardCharsets.UTF_8));
        String forAName = err.toString(StandardCharsets.UTF_8);

        err.reset();
        DocCommand.run(new String[]{"union-membe"}, discard,
                new PrintStream(err, true, StandardCharsets.UTF_8));
        String forAnAnchor = err.toString(StandardCharsets.UTF_8);

        assertTrue(forAName.contains("did you mean: e2015"),
                "a name a section answers to is a name to suggest: " + forAName);
        assertTrue(forAnAnchor.contains("did you mean: union-member"),
                "and so is an anchor written on a paragraph: " + forAnAnchor);
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
