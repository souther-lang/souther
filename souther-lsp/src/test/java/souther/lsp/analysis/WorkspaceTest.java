package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

class WorkspaceTest {

    @Test
    void snapshotScansRootForSoutherSources() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path a = dir.resolve("a.sou");
        Files.writeString(a, "module a exposing ( N )\ndata N = { v: Int }\n");
        Files.writeString(dir.resolve("readme.md"), "not souther");

        Workspace ws = new Workspace();
        ws.setRoots(List.of(dir.toUri().toString()));
        ModuleGraph graph = ws.snapshot(Map.of());

        assertEquals(1, graph.uris().size(), "only the .sou file is picked up");
        assertTrue(graph.text(a.toUri().toString()).contains("data N"));
    }

    @Test
    void snapshotFindsSourcesInNestedDirectories() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path nested = Files.createDirectories(dir.resolve("src/main/souther"));
        Path a = nested.resolve("a.sou");
        Files.writeString(a, "module a\ndata N = { v: Int }\n");

        Workspace ws = new Workspace();
        ws.setRoots(List.of(dir.toUri().toString()));

        assertEquals(1, ws.snapshot(Map.of()).uris().size());
    }

    @Test
    void snapshotReusesTheDiskScanUntilAWatchedChangeInvalidatesIt() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path a = dir.resolve("a.sou");
        Files.writeString(a, "module a\ndata N = { v: Int }\n");
        String uri = a.toUri().toString();

        Workspace ws = new Workspace();
        ws.setRoots(List.of(dir.toUri().toString()));
        ws.snapshot(Map.of());   // first snapshot reads disk

        Files.writeString(a, "module a\ndata N = { v: String }\n");   // changed on disk, not announced
        assertTrue(ws.snapshot(Map.of()).text(uri).contains("Int"),
                "the cached disk scan is reused across snapshots — no re-read per keystroke");

        ws.markChanged();   // workspace/didChangeWatchedFiles
        assertTrue(ws.snapshot(Map.of()).text(uri).contains("String"),
                "after a watched-file change the next snapshot re-reads disk");
    }

    @Test
    void aFolderAddedAfterStartupIsReadAndARemovedOneIsNot() throws Exception {
        Path first = Files.createTempDirectory("ws");
        Path second = Files.createTempDirectory("ws");
        Path a = first.resolve("a.sou");
        Path b = second.resolve("b.sou");
        Files.writeString(a, "module a\ndata A = { v: Int }\n");
        Files.writeString(b, "module b\ndata B = { v: Int }\n");

        Workspace ws = new Workspace();
        ws.setRoots(List.of(first.toUri().toString()));
        assertEquals(Set.of(a.toUri().toString()), Set.copyOf(ws.snapshot(Map.of()).uris()));

        assertTrue(ws.changeRoots(List.of(second.toUri().toString()),
                List.of(first.toUri().toString())), "one folder left and another joined");
        assertEquals(Set.of(b.toUri().toString()), Set.copyOf(ws.snapshot(Map.of()).uris()),
                "the scan is of the roots as they are now");
    }

    @Test
    void aChangeThatLeavesTheRootsAsTheyWereKeepsTheScan() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path a = dir.resolve("a.sou");
        Files.writeString(a, "module a\ndata N = { v: Int }\n");
        String root = dir.toUri().toString();

        Workspace ws = new Workspace();
        ws.setRoots(List.of(root));
        ws.snapshot(Map.of());
        Files.writeString(a, "module a\ndata N = { v: String }\n");   // not announced

        assertFalse(ws.changeRoots(List.of(root), List.of(root)),
                "a folder named as leaving and joining is still a root");
        assertFalse(ws.changeRoots(List.of(root), List.of()), "a root added twice is one root");
        assertTrue(ws.snapshot(Map.of()).text(a.toUri().toString()).contains("Int"),
                "the roots did not change, so neither did what the scan describes");
    }

    @Test
    void anOpenBufferStaysAfterItsFolderLeaves() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path a = dir.resolve("a.sou");
        Files.writeString(a, "module a\ndata N = { v: Int }\n");
        String uri = a.toUri().toString();

        Workspace ws = new Workspace();
        ws.setRoots(List.of(dir.toUri().toString()));
        ws.changeRoots(List.of(), List.of(dir.toUri().toString()));

        assertEquals(List.of(uri), List.copyOf(
                ws.snapshot(Map.of(uri, "module a\ndata N = { v: Int }\n")).uris()),
                "what the editor has open is analysed wherever it is");
    }

    @Test
    void whatIsOnThePathIsFoundOnceUntilAClassOutputIsReported() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Workspace ws = new Workspace();
        ws.setRoots(List.of(dir.toUri().toString()));
        ModulesOnThePath unbuilt = ws.modulesOnThePath();
        assertSame(ModulePath.EMPTY, unbuilt.path(), "nothing has been built");

        Path output = Files.createDirectories(dir.resolve("p/build/classes/java/main"));
        assertSame(unbuilt, ws.modulesOnThePath(), "it is not looked for again on its own");

        ws.filesChanged(List.of(dir.resolve("p/src/a.sou").toUri().toString()));
        assertSame(unbuilt, ws.modulesOnThePath(), "a source says nothing about class output");

        ws.filesChanged(List.of(output.resolve("A.class").toUri().toString()));
        ModulesOnThePath built = ws.modulesOnThePath();
        assertEquals(ModulePath.ofClassPath(List.of(output)), built.path(),
                "a build reported under a class output is found");

        ws.filesChanged(List.of(output.resolve("A.class").toUri().toString()));
        ModulesOnThePath rebuilt = ws.modulesOnThePath();
        assertEquals(built.path(), rebuilt.path(), "built again into the same place");
        assertNotEquals(built, rebuilt,
                "and still not the same modules: what is in that place was written again");
    }

    @Test
    void aChangeOfRootsLooksForClassOutputAgain() throws Exception {
        Path first = Files.createTempDirectory("ws");
        Path second = Files.createTempDirectory("ws");
        Path output = Files.createDirectories(second.resolve("build/classes/java/main"));
        Workspace ws = new Workspace();
        ws.setRoots(List.of(first.toUri().toString()));
        assertSame(ModulePath.EMPTY, ws.modulesOnThePath().path());

        ws.changeRoots(List.of(second.toUri().toString()), List.of());
        assertEquals(ModulePath.ofClassPath(List.of(output)), ws.modulesOnThePath().path());
    }

    /** A project two directories down from a root, the deepest one is looked for at. */
    @Test
    void theClassOutputOfAProjectInAGroupIsFound() throws Exception {
        Path root = Files.createTempDirectory("ws");
        Path output = Files.createDirectories(root.resolve("group/project/build/classes/java/main"));
        Files.createDirectories(root.resolve("group/project/deeper/build/classes/java/main"));
        Workspace ws = new Workspace();
        ws.setRoots(List.of(root.toUri().toString()));

        assertEquals(ModulePath.ofClassPath(List.of(output)), ws.modulesOnThePath().path(),
                "and one further down is not a project this looks for");
    }

    /** What the client is asked to watch, as the protocol's glob text: the output and what is in it. */
    @Test
    void aClassOutputIsWatchedAsTheDirectoryAndWhatIsUnderIt() {
        assertTrue(Workspace.classOutputGlobs().containsAll(List.of(
                "**/build/classes/java/main", "**/build/classes/java/main/**")),
                Workspace.classOutputGlobs().toString());
        assertEquals("**/*.sou", Workspace.sourceGlob());
    }

    @Test
    void anOpenBufferOverlaysTheOnDiskText() throws Exception {
        Path dir = Files.createTempDirectory("ws");
        Path a = dir.resolve("a.sou");
        Files.writeString(a, "module a\ndata N = { v: Int }\n");
        String uri = a.toUri().toString();

        Workspace ws = new Workspace();
        ws.setRoots(List.of(dir.toUri().toString()));
        ModuleGraph graph = ws.snapshot(Map.of(uri, "module a\ndata N = { v: String }\n"));

        assertTrue(graph.text(uri).contains("String"), "the unsaved buffer wins over disk");
    }
}
