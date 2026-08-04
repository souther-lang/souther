package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.LspDiagnostic;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stand-in and the row it contradicts are one problem, and they need not be in one file. The
 * editor gets a marker in each of them, on the statement that file actually wrote, and each marker
 * links to the other.
 */
class AProblemWrittenInTwoFilesIsMarkedInBothTest {

    private static final String MODULE_URI = "file:///clash.sou";
    private static final String ATTACHED_URI = "file:///clash.examples.sou";

    private static final String MODULE = """
            module example.clash

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            example findMember
                | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
            """;

    private static final String ATTACHED = """
            examples for example.clash

            fake findMember
                | (MemberId("m-1")) -> Missing { why = "no such member" }
            """;

    private static Map<String, List<LspDiagnostic>> published() {
        ModuleGraph graph = ModuleGraph.of(Map.of(MODULE_URI, MODULE, ATTACHED_URI, ATTACHED));
        return new Analyzer().diagnostics(graph);
    }

    private static LspDiagnostic disagreementIn(Map<String, List<LspDiagnostic>> byUri, String uri) {
        List<LspDiagnostic> here = byUri.getOrDefault(uri, List.of()).stream()
                .filter(d -> "E1919".equals(d.code()))
                .toList();
        assertEquals(1, here.size(), uri + " has one: " + byUri);
        return here.get(0);
    }

    @Test
    void bothFilesGetOneMarker() {
        Map<String, List<LspDiagnostic>> byUri = published();

        disagreementIn(byUri, MODULE_URI);
        disagreementIn(byUri, ATTACHED_URI);
    }

    @Test
    void eachMarkerSitsOnTheStatementItsOwnFileWrote() {
        Map<String, List<LspDiagnostic>> byUri = published();

        LspDiagnostic onRow = disagreementIn(byUri, MODULE_URI);
        LspDiagnostic onFake = disagreementIn(byUri, ATTACHED_URI);

        assertEquals(9, onRow.range().start().line(), "the recorded row, 0-based");
        assertEquals(3, onFake.range().start().line(), "the fake row, 0-based");
        assertNotEquals(onRow.range(), onFake.range(),
                "the second file is not marked at a line copied from the first");
    }

    @Test
    void eachMarkerLinksToTheOtherHalf() {
        Map<String, List<LspDiagnostic>> byUri = published();

        LspDiagnostic onRow = disagreementIn(byUri, MODULE_URI);
        assertEquals(List.of(ATTACHED_URI),
                onRow.related().stream().map(LspDiagnostic.Related::uri).toList());
        assertEquals(3, onRow.related().get(0).range().start().line(), "at the fake row");

        LspDiagnostic onFake = disagreementIn(byUri, ATTACHED_URI);
        assertEquals(List.of(MODULE_URI),
                onFake.related().stream().map(LspDiagnostic.Related::uri).toList());
        assertEquals(9, onFake.related().get(0).range().start().line(), "at the recorded row");
    }

    @Test
    void bothMarkersSayTheSameThingAndAreWarnings() {
        Map<String, List<LspDiagnostic>> byUri = published();

        LspDiagnostic onRow = disagreementIn(byUri, MODULE_URI);
        LspDiagnostic onFake = disagreementIn(byUri, ATTACHED_URI);

        assertEquals(onRow.message(), onFake.message());
        assertTrue(onRow.message().contains("findMember"), onRow.message());
        assertEquals(LspDiagnostic.WARNING, onRow.severity());
        assertEquals(LspDiagnostic.WARNING, onFake.severity());
    }
}
