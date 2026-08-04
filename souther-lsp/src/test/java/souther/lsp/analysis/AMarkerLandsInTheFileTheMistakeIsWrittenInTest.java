package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.LspDiagnostic;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An author renames a case in the model and leaves a row in the attached file still naming the old
 * one. In the editor the marker used to land on the model file, at the line number the row happened
 * to have — an unrelated declaration — while the file that actually holds the mistake was left
 * without a squiggle at all (issue #309).
 *
 * <p>A marker goes in the file the writing it is about was written in, which for an
 * {@code examples for} file's rows is that file.
 */
class AMarkerLandsInTheFileTheMistakeIsWrittenInTest {

    private static final String MODEL_URI = "file:///shippingfee.sou";
    private static final String ATTACHED_URI = "file:///shippingfee.examples.sou";
    private static final String RENAMED_URI = "file:///rows/shippingfee.examples.sou";

    /** Long enough that a coordinate from the short file beside it lands on an unrelated line. */
    private static final String MODEL = """
            module shippingfee

            data 都道府県 = { 名前: String }
            data 数量     = { 個数: Int }
            data 送料     = { 円: Int }

            behavior 送料を求める : (県: 都道府県, 数: 数量) -> 送料
                constructs 送料

            let 送料を求める (県, 数) = 送料 { 円 = 数.個数 * 100 }

            data 一般 = { 名前: String }
            """;

    /** A row still naming `北海道沖縄`, which the model no longer has. */
    private static final String ATTACHED = """
            examples for shippingfee

            example 送料を求める
                | "北海道" : (北海道沖縄, 数量 { 個数 = 1 }) -> 送料 { 円 = 100 }
            """;

    private static Map<String, List<LspDiagnostic>> publishedBy(Analyzer analyzer,
                                                                Map<String, String> sources) {
        return analyzer.diagnostics(ModuleGraph.of(sources));
    }

    private static Map<String, List<LspDiagnostic>> asWritten() {
        return publishedBy(new Analyzer(), Map.of(MODEL_URI, MODEL, ATTACHED_URI, ATTACHED));
    }

    private static List<LspDiagnostic> on(Map<String, List<LspDiagnostic>> byUri, String uri) {
        return byUri.getOrDefault(uri, List.of());
    }

    @Test
    void aWorkspaceMarksAnAttachedFilesMistakeInThatDocument() {
        List<LspDiagnostic> here = on(asWritten(), ATTACHED_URI);

        assertEquals(1, here.size(), "the row that names it is written here: " + here);
        assertEquals(3, here.get(0).range().start().line(),
                "on the row, which is the fourth line and so line 3 zero-based");
    }

    @Test
    void theModelFilesDocumentIsLeftClean() {
        assertEquals(List.of(), on(asWritten(), MODEL_URI),
                "the model declares nothing wrong, so it gets no squiggle");
    }

    /**
     * The file a position was read from is part of what makes it that position, so a document that
     * moves takes its diagnostics with it. Renaming without editing is the case that would go wrong
     * if provenance were carried alongside a position rather than in it: nothing about the text
     * changes, so nothing downstream would be recomputed and the marker would be left on a URI the
     * workspace no longer has.
     */
    @Test
    void aMarkerMovesWhenAnAttachedFileIsRenamedWithoutChangingItsContents() {
        // One analyzer across both, so the second reading goes through the workspace compile it
        // already has — the incremental path, which is where this could go wrong.
        Analyzer analyzer = new Analyzer();
        Map<String, List<LspDiagnostic>> before =
                publishedBy(analyzer, Map.of(MODEL_URI, MODEL, ATTACHED_URI, ATTACHED));
        assertEquals(1, on(before, ATTACHED_URI).size(), "it starts on the first URI: " + before);

        Map<String, List<LspDiagnostic>> after =
                publishedBy(analyzer, Map.of(MODEL_URI, MODEL, RENAMED_URI, ATTACHED));

        assertEquals(List.of(), on(after, ATTACHED_URI), "gone from the URI that no longer exists");
        assertEquals(1, on(after, RENAMED_URI).size(), "and on the one that does: " + after);
        assertEquals(List.of(), on(after, MODEL_URI), "and still not on the model file");
    }

    /** The marker is on the name the author has to change, not merely in the right file. */
    @Test
    void theMarkerSitsOnTheNameThatDenotesNothing() {
        LspDiagnostic only = on(asWritten(), ATTACHED_URI).get(0);
        String row = ATTACHED.lines().toList().get(3);

        assertTrue(row.substring(only.range().start().character()).startsWith("北海道沖縄"),
                "the squiggle starts at the name: " + only.range());
    }
}
