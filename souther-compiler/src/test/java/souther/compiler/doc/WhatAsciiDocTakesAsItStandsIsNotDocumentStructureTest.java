package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A listing, a literal block, a passthrough and a comment block are shown as they stand or not
 * shown at all, and AsciiDoc reads no structure out of any of them. What this document reads out of
 * them has to be nothing too.
 *
 * <p>A name is the smaller half of it. A heading read where AsciiDoc reads none ends the section
 * around it, so the two would disagree about where the sections are — the surrounding section would
 * come back cut off at a heading no reader is shown, which is a wrong answer to a right question
 * rather than an extra answer to a wrong one.
 */
class WhatAsciiDocTakesAsItStandsIsNotDocumentStructureTest {

    private static String document(String delimiter) {
        return """
                = A specification

                [#real]
                == The section that is really there

                What it says.

                %s
                [#hidden]
                == A heading that is only shown, or not shown at all

                [#also-hidden]
                What that block says.
                %s

                The rest of what the real section says.
                """.formatted(delimiter, delimiter);
    }

    @ParameterizedTest
    @ValueSource(strings = {"----", "....", "++++", "////"})
    void aHeadingInsideAnOpaqueBlockIsNotASection(String delimiter) {
        SpecDocument spec = SpecDocument.of(document(delimiter));

        assertEquals(1, spec.sections().size(),
                "only the heading outside the block is a section: "
                        + spec.sections().stream().map(SpecDocument.Section::anchor).toList());
        assertNull(spec.section("hidden"), "and it is not answered for by name either");
    }

    @ParameterizedTest
    @ValueSource(strings = {"----", "....", "++++", "////"})
    void anAnchorInsideAnOpaqueBlockIsNotAName(String delimiter) {
        SpecDocument spec = SpecDocument.of(document(delimiter));

        assertNull(spec.section("also-hidden"),
                "an anchor written where AsciiDoc registers no target is no name to ask for");
        assertNotNull(spec.section("real"), "the section around it still answers");
    }

    @ParameterizedTest
    @ValueSource(strings = {"----", "....", "++++", "////"})
    void aHeadingInsideAnOpaqueBlockDoesNotEndTheSectionAroundIt(String delimiter) {
        SpecDocument spec = SpecDocument.of(document(delimiter));

        assertTrue(spec.section("real").body().contains("The rest of what the real section says."),
                "the section runs past the block, having never been ended by it: "
                        + spec.section("real").body());
    }

    @Test
    void aBlockIsEndedByTheDelimiterItWasOpenedWithAndNotByAShorterOne() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#real]
                == The section that is really there

                -----
                ----
                [#hidden]
                == Still inside the longer listing

                ----
                -----

                The rest of it.
                """);

        assertEquals(1, spec.sections().size(), "the inner run is content, not the end of the block");
        assertNull(spec.section("hidden"));
    }
}
