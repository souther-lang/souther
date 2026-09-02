package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Nothing that decides what a document writes reaches what writes it.
 *
 * <p>The two are a stage apart on purpose. What a place a reader is sent to is, which of several
 * such places a document writes, and what order the entries of an array come in are settled from
 * the values alone; recording that a source has been named and now owes an explanation happens
 * afterwards, while the document is being written.
 *
 * <p><b>Run together, the second decides the first.</b> The table of sources a document explains
 * keeps the order the identities were first written in, so a comparison that asked what a source is
 * called would put it in that table — and which entries a sort compares, and how often, is a fact
 * about the sorting algorithm. An order over places would then be settling one order and creating
 * another that nothing decided, one stage further out.
 *
 * <p>Held as a rule about the packages rather than about the one method it was noticed in. What
 * deciding needs is the values and never the writer, so a decider that reaches anything of the
 * writer's is one that could reach that.
 */
class DecidingWhatADocumentWritesDoesNotTouchTheWriterTest {

    private static final String DECIDES = "souther.compiler.publish.";
    private static final String WRITES = "souther.compiler.report.";

    @Test
    void nothingThatDecidesWhatIsWrittenNamesAnythingThatWritesIt() throws Exception {
        List<String> reaching = new ArrayList<>();
        boolean any = false;
        for (Compiled.Site site : Compiled.sites()) {
            if (!site.from().startsWith(DECIDES)) {
                continue;
            }
            any = true;
            if (site.owner().startsWith(WRITES)) {
                reaching.add(site.at() + " reaches " + site.owner() + "." + site.member());
            }
        }

        assertTrue(any, "nothing that decides what a document writes does anything at all, so this"
                + " is passing for the wrong reason");
        assertEquals(List.of(), reaching,
                "something that decides what a document writes reaches what writes it, so what it"
                        + " decides can depend on what has been written so far");
    }
}
