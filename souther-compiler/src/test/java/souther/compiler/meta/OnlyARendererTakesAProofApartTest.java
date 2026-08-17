package souther.compiler.meta;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What decides a policy reads the answer, and what writes a sentence reads the proof.
 *
 * <p>{@code Reachability} has three arms and each of them carries something: why nothing arrives,
 * what says something does, why nothing settled it. A reader that took one of those apart would be
 * deciding an obligation, a diagnostic or a claim on a distinction inside the payload — and a
 * distinction added there later would silently become a change to that decision. Kept out, an arm
 * added to a proof is a compile error in one place and a change to no policy.
 *
 * <p>Measured over the sources rather than argued for. The rule is worth nothing if the next reader
 * to want a nicer sentence reaches for the proof where they stand.
 */
class OnlyARendererTakesAProofApartTest {

    /**
     * The places a payload is turned into words: the dead-branch warning, and the projection that
     * writes what a report says about a claim nothing settled.
     *
     * <p>Named by file rather than by a marker, because what makes one of these a renderer is that
     * a sentence is written there and nothing else about it. A third is a decision to take, not
     * something to let in by writing an annotation.
     */
    private static final List<String> RENDERERS =
            List.of("Adequacy.java", "ClaimAnnotations.java");

    /**
     * The payloads. Taking one apart means naming one of its arms in a pattern or a test.
     *
     * <p>Asked of the files that name the package these live in. {@code Witness} is a word other
     * readings use for their own types — a formatter's evidence, the arms a comparison's line can
     * be met from — and a scan by spelling would answer about those, which is a different question
     * from this one.
     */
    private static final Pattern TAKES_APART = Pattern.compile(
            "\\b(?:Proof|Witness|WhyUnsettled)\\s*\\.\\s*[A-Z][A-Za-z]*");

    /** What names the answer's own package, and so is talking about these types. */
    private static final String THE_PACKAGE = "souther.compiler.reach";

    @Test
    void nothingButARendererNamesAnArmOfAProof() throws IOException {
        List<String> offenders = new ArrayList<>();
        for (Path source : EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources()) {
            String name = source.getFileName().toString();
            // The payloads' own declarations say what their arms are; that is not reading one.
            if (RENDERERS.contains(name) || isPartOfTheAnswer(source)) {
                continue;
            }
            String text = Files.readString(source, StandardCharsets.UTF_8);
            if (!text.contains(THE_PACKAGE)) {
                continue;   // whatever it calls a witness, it is not one of these
            }
            Matcher m = TAKES_APART.matcher(text);
            while (m.find()) {
                // A javadoc link is a reference and not a reading. What is being looked for is code
                // that branches on which arm it got.
                if (!text.startsWith("{@link ", Math.max(0, m.start() - "{@link ".length()))) {
                    offenders.add(name + ": " + m.group());
                }
            }
        }
        assertEquals(List.of(), offenders,
                "these read inside an answer they should be deciding from the arms of");
    }

    /** Whether the file is one of the answer's own types, or the walk that builds them. */
    private static boolean isPartOfTheAnswer(Path source) {
        String path = source.toString();
        return path.contains(Path.of("souther", "compiler", "reach").toString())
                || source.getFileName().toString().equals("PathReachability.java");
    }

    /** The check is worth having only if it can fail. */
    @Test
    void andTheRendererIsOneThatDoes() throws IOException {
        String rendered = Files.readString(
                Path.of("src", "main", "java", "souther", "compiler", "query", "Adequacy.java")
                        .toAbsolutePath(),
                StandardCharsets.UTF_8);
        assertFalse(TAKES_APART.matcher(rendered).results().toList().isEmpty(),
                "the renderer names no arm of a proof, so this test forbids nothing");
    }
}
