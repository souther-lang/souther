package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import souther.compiler.inputs.BlockReason;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The word an adequacy document writes is written in one place.
 *
 * <p>{@link BlockReason} is what this compiler could not do and {@link UndividedPosition.Reason} is
 * what a document promises its reader they can tell apart. The two are kept at different speeds on
 * purpose: a capability gained here removes a case here and need not move a published vocabulary.
 * That only holds while one projection sits between them — a second producer naming a published
 * word is a reader deciding for itself what the document says, and the coarsening stops being
 * reviewable in one place.
 *
 * <p>Held over the sources because it is not a thing a type can say. The published words are an
 * enum and anything can name one; what is being held is that nothing does.
 *
 * <p>A tripwire and not a proof. A constant lifted into a field, or a switch that returns one from
 * somewhere else, defeats it — and the reading that would have to be added first is the one this
 * fails on.
 */
class OneProjectionWritesTheWordADocumentReadsTest {

    @Test
    void nothingButTheProjectionNamesAPublishedReason() throws IOException {
        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        Set<String> naming = new TreeSet<>();
        for (Path source : sources) {
            String text = Files.readString(source, StandardCharsets.UTF_8);
            if (text.contains("UndividedPosition.Reason.")) {
                naming.add(source.getFileName().toString());
            }
        }

        assertEquals(Set.of("ReportedReason.java"), naming,
                "a published reason is written by the one projection; a producer naming one has"
                        + " decided for itself what the document says");
    }

    /** And the projection answers every reason there is, which the switch holds — this says the
     *  switch is reached at all, over the cases a reader here can name. */
    @Test
    void everyInternalReasonHasAWordToBeSaidIn() {
        List<BlockReason> all = List.of(
                new BlockReason.TypeUnresolved(),
                new BlockReason.DepthLimit(),
                new BlockReason.UnsupportedTraversal(BlockReason.Traversal.MAPPING_CONTENT),
                new BlockReason.UnreadComparisonForm(),
                new BlockReason.UnreadComparisonDomain(),
                new BlockReason.ComparisonBetweenPositions());

        for (BlockReason each : all) {
            assertFalse(ReportedReason.of(each) == null, each + " has a word");
        }
        assertEquals(1, all.stream().map(ReportedReason::of).distinct().toList().stream()
                        .filter(word -> word == UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL)
                        .count(),
                "the three traversals are one word, which is the coarsening this projection is for");
    }
}
