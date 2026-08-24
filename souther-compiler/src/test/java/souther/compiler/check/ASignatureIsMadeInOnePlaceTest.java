package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Making a behavior's signature is what admits what its boundary carries, and it happens once.
 *
 * <p>{@link Sig}'s constructor is package-private, so nothing outside {@code check} can assemble one
 * out of shapes nothing admitted. That closes the wrong kind of signature; it does not close a
 * second walk. Two callers of {@link PipelineSigs#signatures} would each build a correct answer, and
 * the phase below the check would read one of them while the check read the other — the boundary's
 * question answered twice, which is what carrying the answer was for. Nothing an ordinary test can
 * observe would change: the two walks are the same walk, so their answers agree, and they agree
 * until the day the trees they are given stop being the same tree.
 *
 * <p>So it is asked of the sources. This is a tripwire and not a proof — a helper in between defeats
 * it — but the call that would have to be added first is the one this fails on.
 */
class ASignatureIsMadeInOnePlaceTest {

    /** Where a signature is made: the query that owns the answer, and hands it to the check, the
     *  backend and whoever drives a behavior. */
    private static final String THE_ONE_PLACE = "query/Bodies.java";

    @Test
    void everySignatureComesFromTheOneQueryThatMakesThem() throws IOException {
        List<Path> sources = mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        List<String> callers = new ArrayList<>();
        for (Path source : sources) {
            String text = Files.readString(source, StandardCharsets.UTF_8);
            // The declaration itself, and prose naming it, are not calls.
            if (source.endsWith(Path.of("check", "PipelineSigs.java"))
                    || !text.contains("PipelineSigs.signatures(")) {
                continue;
            }
            callers.add(source.getParent().getFileName() + "/" + source.getFileName());
        }
        assertEquals(List.of(THE_ONE_PLACE), callers,
                "a signature is made in one place; these build their own");
    }

    private static List<Path> mainSources() throws IOException {
        return RepositoryLayout.ofWorkingDirectory().mainJavaSources();
    }
}
