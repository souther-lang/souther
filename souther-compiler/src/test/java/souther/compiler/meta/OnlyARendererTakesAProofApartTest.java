package souther.compiler.meta;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What decides a policy reads the answer, and what writes a sentence writes one payload's words.
 *
 * <p>{@code Reachability} has three arms and each carries something: why nothing arrives, what says
 * something does, why nothing settled it. A reader that took one of those apart would be deciding
 * an obligation, a diagnostic or a claim on a distinction inside the payload — and a distinction
 * added there later would silently become a change to that decision. Kept out, an arm added to a
 * payload is a compile error in one place and a change to no policy.
 *
 * <p><b>Held by the types first, and measured here second.</b> The arms of a proof, a witness and a
 * reason are package-private in {@code souther.compiler.reach}, so nothing outside can name one: a
 * reader gets at what one holds by implementing its {@code Words}, which is a compile error the day
 * an arm is added and no error at all when it is not. That is the guarantee; a scan cannot be one,
 * since a nested import, a simple name or a qualified constructor walks round any spelling it looks
 * for.
 *
 * <p>What is left for a scan is the thing the compiler has no word for: which file may write which
 * payload's sentences. A file allowed to write a proof's is not thereby allowed to write a reason's
 * — those are different sentences by different readers, and one exemption would let either grow
 * into the other without anything saying so.
 */
class OnlyARendererTakesAProofApartTest {

    /**
     * Which file may take each payload apart, and nothing else may.
     *
     * <p>Named by file rather than by a marker, because what makes one of these its reader is that
     * a sentence about that payload is written there. A second reader is a decision to take, not
     * something to let in by writing an annotation.
     */
    private static final Map<String, String> READS = Map.of(
            // how it was shown that nothing arrives -> the dead-branch warning
            "Proof", "Adequacy.java",
            // why nothing settled it -> what a report says about a claim
            "WhyUnsettled", "ClaimAnnotations.java");

    /** What says something arrives. Nothing writes a sentence about one yet, so nothing reads one
     *  apart — and the day something does, this is where that is decided. */
    private static final List<String> READ_BY_NOBODY = List.of("Witness");

    /** The one place any of them is built. An answer assembled by a consumer is a consumer deciding
     *  what the reading should have said. */
    private static final String BUILDER = "PathReachability.java";

    /** What names the answer's own package, and so is talking about these types. {@code Witness} is
     *  a word other readings use for their own — a formatter's evidence, the arms a comparison's
     *  line can be met from — and a scan by spelling would answer about those. */
    private static final String THE_PACKAGE = "souther.compiler.reach";

    /** Writing a payload's sentences is implementing its {@code Words}. Nothing else can. */
    private static Pattern namesAnArmOf(String payload) {
        return Pattern.compile("\\b" + payload + "\\s*\\.\\s*Words\\b");
    }

    private static final Pattern BUILDS =
            Pattern.compile("\\b(?:Proof|Witness|WhyUnsettled|Reachability)\\s*\\.\\s*"
                    + "(?:conditionsThatCannotAllHold|everyCaseRefused|aRunWentThrough"
                    + "|everyRuleReadAndNothingAbove|noWitness|aConditionWasNotRead"
                    + "|thePositionDidNotSettleIt|theWalkDidNotReachIt)\\s*\\(");

    @Test
    void eachPayloadsSentencesAreWrittenByItsOwnReaderAndNoOther() throws IOException {
        List<String> offenders = new ArrayList<>();
        for (Path source : sourcesThatNameThePackage()) {
            String name = source.getFileName().toString();
            // The reading that makes these names every arm it makes, which is building and not
            // taking apart. What it may not do is decide anything by which arm it got, and the rule
            // below is what holds it to that: nothing else builds one at all.
            if (name.equals(BUILDER)) {
                continue;
            }
            String text = Files.readString(source, StandardCharsets.UTF_8);
            READS.forEach((payload, reader) -> {
                if (!name.equals(reader)) {
                    offenders.addAll(namesOf(namesAnArmOf(payload), text, name));
                }
            });
            for (String payload : READ_BY_NOBODY) {
                offenders.addAll(namesOf(namesAnArmOf(payload), text, name));
            }
        }
        assertEquals(List.of(), offenders,
                "these write sentences for a payload that is not theirs to write");
    }

    @Test
    void andNothingButTheReadingBuildsOne() throws IOException {
        List<String> offenders = new ArrayList<>();
        for (Path source : sourcesThatNameThePackage()) {
            String name = source.getFileName().toString();
            if (name.equals(BUILDER)) {
                continue;
            }
            offenders.addAll(namesOf(BUILDS,
                    Files.readString(source, StandardCharsets.UTF_8), name));
        }
        assertEquals(List.of(), offenders, "these make an answer the reading did not make");
    }

    /** The checks are worth having only if they can fail. */
    @Test
    void andEachReaderIsOneThatDoes() throws IOException {
        for (Map.Entry<String, String> each : READS.entrySet()) {
            String text = Files.readString(sourceNamed(each.getValue()), StandardCharsets.UTF_8);
            assertFalse(namesAnArmOf(each.getKey()).matcher(text).results().toList().isEmpty(),
                    each.getValue() + " names no arm of " + each.getKey()
                            + ", so this test forbids nothing");
        }
        assertFalse(BUILDS.matcher(Files.readString(sourceNamed(BUILDER), StandardCharsets.UTF_8))
                        .results().toList().isEmpty(),
                BUILDER + " builds no answer, so the rule above forbids nothing");
    }

    /** The places a match is a reading rather than a reference. A javadoc link names a type; it
     *  does not branch on which arm it got. */
    private static List<String> namesOf(Pattern what, String text, String file) {
        List<String> found = new ArrayList<>();
        Matcher m = what.matcher(text);
        while (m.find()) {
            if (!text.startsWith("{@link ", Math.max(0, m.start() - "{@link ".length()))) {
                found.add(file + ": " + m.group());
            }
        }
        return found;
    }

    /** Every main source that talks about these types at all, the answers' own declarations aside:
     *  what an arm is, is what those files say. */
    private static List<Path> sourcesThatNameThePackage() throws IOException {
        List<Path> found = new ArrayList<>();
        for (Path source : EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources()) {
            if (source.toString().contains(Path.of("souther", "compiler", "reach").toString())) {
                continue;
            }
            if (Files.readString(source, StandardCharsets.UTF_8).contains(THE_PACKAGE)) {
                found.add(source);
            }
        }
        return found;
    }

    private static Path sourceNamed(String name) throws IOException {
        return sourcesThatNameThePackage().stream()
                .filter(each -> each.getFileName().toString().equals(name))
                .findFirst()
                .orElseThrow(() -> new AssertionError(
                        name + " does not name " + THE_PACKAGE + "; this test names the wrong file"));
    }
}
