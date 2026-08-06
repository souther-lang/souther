package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The language specification is a resource of the compiler jar, so `souther doc` answers from the
 * same version the compiler was built from — not from whatever file happens to be on disk.
 */
class TheSpecificationTravelsWithTheCompilerTest {

    @Test
    void theBundledSpecificationListsItsSectionsInDocumentOrder() {
        SpecDocument spec = SpecDocument.bundled();

        List<SpecDocument.Section> sections = spec.sections();

        assertTrue(sections.size() > 100, "the specification has its full section count, got " + sections.size());
        assertEquals("purpose", sections.getFirst().anchor());
        assertEquals("Purpose", sections.getFirst().title());
    }

    @Test
    void aSectionIsReadBackByItsAnchorWithItsBody() {
        SpecDocument spec = SpecDocument.bundled();

        SpecDocument.Section section = spec.section("purpose");

        assertTrue(section.body().contains("JVM-targeted language"),
                "the purpose section carries its own prose");
    }
}
