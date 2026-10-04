package souther.lsp.analysis;

import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@link ModuleGraph} is the workspace as it was when it was made, and a reader that holds one
 * between two requests, or takes two of them to be the same by identity, depends on that.
 *
 * <p>What it is made from is copied once, inside the graph, and what it hands out refuses a change.
 * So the editor's documents changing after a snapshot, a caller changing the map it gave, and a
 * reader calling {@code remove} on the URIs it was handed all leave the graph as it was.
 */
class ASnapshotOfTheWorkspaceIsChangedByNothingThatReadsItTest {

    private static final String URI = "file:///a.sou";

    private static final String TEXT = "module a\ndata N = { v: Int }\n";

    @Test
    void theUrisAGraphHandsOutRefuseAChange() {
        ModuleGraph graph = ModuleGraph.of(Map.of(URI, TEXT));

        assertThrows(UnsupportedOperationException.class, () -> graph.uris().clear());
        assertThrows(UnsupportedOperationException.class, () -> graph.uris().remove(URI));
        assertEquals(List.of(URI), List.copyOf(graph.uris()));
    }

    @Test
    void theUrisOfAGraphOverlayingDiskRefuseAChangeToo() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path onDisk = Files.writeString(dir.resolve("a.sou"), TEXT);
        Workspace workspace = new Workspace();
        workspace.setRoots(List.of(dir.toUri().toString()));

        ModuleGraph graph = workspace.snapshot(Map.of());

        assertThrows(UnsupportedOperationException.class, () -> graph.uris().clear());
        assertEquals(List.of(onDisk.toUri().toString()), List.copyOf(graph.uris()));
    }

    @Test
    void aMapGivenToAGraphIsCopiedAndNotKept() {
        Map<String, String> given = new LinkedHashMap<>(Map.of(URI, TEXT));
        ModuleGraph graph = ModuleGraph.of(given);

        given.put("file:///b.sou", "module b\n");
        given.put(URI, "module changed\n");

        assertEquals(List.of(URI), List.copyOf(graph.uris()));
        assertEquals(TEXT, graph.text(URI));
        assertTrue(graph.isOpen(URI));
    }

    @Test
    void anEditAfterASnapshotLeavesTheSnapshotAsItWas() {
        Workspace workspace = new Workspace();
        DocumentStore documents = new DocumentStore();
        documents.open(URI, TEXT);

        ModuleGraph before = workspace.snapshot(documents);
        documents.change(URI, "module a\ndata N = { v: String }\n");
        documents.close(URI);
        documents.open("file:///b.sou", "module b\n");

        assertEquals(TEXT, before.text(URI));
        assertEquals(List.of(URI), List.copyOf(before.uris()));
        assertTrue(before.isOpen(URI));
    }

    @Test
    void theUrisOfTheOpenDocumentsRefuseAChange() {
        DocumentStore documents = new DocumentStore();
        documents.open(URI, TEXT);

        assertThrows(UnsupportedOperationException.class, () -> documents.uris().clear());
        assertThrows(UnsupportedOperationException.class, () -> documents.uris().remove(URI));
        assertEquals(TEXT, documents.get(URI));
    }

    @Test
    void aSourceIsOpenOnlyIfABufferOfTheEditorIsWhereItCameFrom() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path onDisk = Files.writeString(dir.resolve("a.sou"), TEXT);
        Path alsoOnDisk = Files.writeString(dir.resolve("b.sou"), "module b\n");
        String a = onDisk.toUri().toString();
        String b = alsoOnDisk.toUri().toString();
        Workspace workspace = new Workspace();
        workspace.setRoots(List.of(dir.toUri().toString()));

        ModuleGraph graph = workspace.snapshot(Map.of(a, "module a\ndata N = { v: String }\n"));

        assertTrue(graph.isOpen(a));
        assertFalse(graph.isOpen(b));
        assertFalse(graph.isOpen("file:///nowhere.sou"));
    }
}
