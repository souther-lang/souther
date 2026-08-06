package souther.compiler;

import net.unit8.raoh.Issue;
import net.unit8.raoh.Issues;
import net.unit8.raoh.MessageKeys;
import net.unit8.raoh.ResourceBundleMessageResolver;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a decode failure says once the decoder's catalog has had its turn. An issue names the
 * constraint that rejected the value, not only the code classifying it, so a code covering several
 * constraints — {@code out_of_range} states a lower bound, an upper bound, or both — is described as
 * the one it is. Where no entry applies, the message the decoder already wrote stands: a rule no
 * constraint states carries the rejecting type and clause, and losing that to the code's own name
 * told the reader nothing (issues #365, #371).
 */
class DecodeMessageLocalizationTest {

    @TempDir
    java.nio.file.Path dir;

    private java.nio.file.Path write(String fileName, String source) throws Exception {
        java.nio.file.Path file = dir.resolve(fileName);
        Files.writeString(file, source);
        return file;
    }

    /** The catalog `souther run` reads its issues against. */
    private static final ResourceBundleMessageResolver CATALOG =
            new ResourceBundleMessageResolver("net.unit8.raoh.messages");

    /** Anything a catalog template would have written and no substitution reached. */
    private static final Pattern UNFILLED = Pattern.compile("\\{[A-Za-z][A-Za-z0-9_]*}");

    private static void namesNoPlaceholder(String rendered) {
        Matcher m = UNFILLED.matcher(rendered);
        assertFalse(m.find(), "a placeholder reached the reader: " + rendered);
    }

    /** The failure of running {@code source} against {@code input}, as the reader sees it in
     *  {@code locale}. */
    private String rendered(String fileName, String source, String input, Locale locale)
            throws Exception {
        Runner.RunException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(write(fileName, source), null, input));
        return e.localized(locale);
    }

    private static String intBounded(String module, String clause) {
        return """
                module %s

                data T = Int
                    invariant %s

                behavior echo : (a: T) -> T

                let echo (a) = a
                """.formatted(module, clause);
    }

    private static String decimalBounded(String module, String clause) {
        return """
                module %s

                data T = Decimal
                    invariant %s

                behavior echo : (a: T) -> T

                let echo (a) = a
                """.formatted(module, clause);
    }

    // --- a bound stated on one side only ---

    @Test
    void aLowerBoundOnlyNamesTheBoundItStates() throws Exception {
        String en = rendered("ge0.sou", intBounded("ge0", "value >= 0"), "-1", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertTrue(en.contains("must be non-negative"), en);
    }

    @Test
    void anUpperBoundOnlyNamesTheBoundItStates() throws Exception {
        String en = rendered("le100.sou", intBounded("le100", "value <= 100"), "101", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertTrue(en.contains("100"), en);
    }

    @Test
    void aLowerBoundAwayFromZeroNamesItsNumber() throws Exception {
        String en = rendered("ge5.sou", intBounded("ge5", "value >= 5"), "4", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertTrue(en.contains("5"), en);
    }

    /** A one-sided bound has an entry of its own, so the reader gets it in their language and it
     *  states the one end the rule has. */
    @Test
    void aOneSidedBoundIsStatedInTheReadersLanguage() throws Exception {
        String ja = rendered("ge0ja.sou", intBounded("ge0ja", "value >= 0"), "-1", Locale.JAPANESE);
        namesNoPlaceholder(ja);
        assertTrue(ja.contains("以上"), ja);
        assertFalse(ja.contains("以下"), "no upper bound is stated by `value >= 0`: " + ja);
    }

    @Test
    void anUpperBoundOnlyIsStatedInTheReadersLanguage() throws Exception {
        String ja = rendered("le100ja.sou", intBounded("le100ja", "value <= 100"), "101",
                Locale.JAPANESE);
        namesNoPlaceholder(ja);
        assertTrue(ja.contains("100") && ja.contains("以下"), ja);
        assertFalse(ja.contains("以上"), "no lower bound is stated by `value <= 100`: " + ja);
    }

    /** A Decimal bound reaches the same constraints as an Int one, and the same catalog entries. */
    @Test
    void aDecimalBoundNamesTheBoundItStates() throws Exception {
        String en = rendered("dge.sou", decimalBounded("dge", "value >= 0.0m"), "-1.0", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertTrue(en.contains("must be non-negative"), en);
    }

    /** {@code > 0} and {@code >= 0} admit different values, so they cannot read alike. Both carry
     *  {@code min = 0} in the metadata, so what tells them apart is the constraint each issue names,
     *  not the bound it carries. */
    @Test
    void aStrictDecimalBoundReadsDifferentlyFromAnInclusiveOne() throws Exception {
        String strict = rendered("dgt.sou", decimalBounded("dgt", "value > 0.0m"), "0.0",
                Locale.JAPANESE);
        String inclusive = rendered("dge2.sou", decimalBounded("dge2", "value >= 0.0m"), "-1.0",
                Locale.JAPANESE);
        namesNoPlaceholder(strict);
        namesNoPlaceholder(inclusive);
        assertNotEqualsIgnoringPrefix(strict, inclusive);
    }

    /** The two failures differ in the part the decoder wrote, not only in the runner's own wording
     *  around it. */
    private static void assertNotEqualsIgnoringPrefix(String a, String b) {
        String reasonA = a.substring(a.indexOf("(root): "));
        String reasonB = b.substring(b.indexOf("(root): "));
        assertFalse(reasonA.equals(reasonB),
                "a rule that rejects 0 cannot read as one that admits it: " + reasonA);
    }

    /** An invariant written with {@code &&} is two constraints, each stating one side. Whichever one
     *  the value breaks reports alone, so a two-sided invariant still renders a one-sided message. */
    @Test
    void aTwoSidedInvariantReportsWhicheverSideBroke() throws Exception {
        String source = intBounded("both", "value >= 0 && value <= 100");
        String low = rendered("both.sou", source, "-1", Locale.ENGLISH);
        String high = rendered("both2.sou", source.replace("module both", "module both2"), "101",
                Locale.ENGLISH);
        namesNoPlaceholder(low);
        namesNoPlaceholder(high);
        assertTrue(high.contains("100"), high);
    }

    /** An empty list is rejected as empty rather than as one element short of a bound, which is what
     *  the constraint the mapping chose actually says. */
    @Test
    void anEmptyListIsStatedAsEmptiness() throws Exception {
        String ja = rendered("lne.sou", """
                module lne

                data T = List<Int>
                    invariant List.length(value) >= 1

                behavior echo : (a: T) -> T

                let echo (a) = a
                """, "[]", Locale.JAPANESE);
        namesNoPlaceholder(ja);
        assertTrue(ja.contains("空"), ja);
    }

    // --- a rule no constraint states ---

    /** A clause the mapping cannot prove equivalent keeps its own check and reports the shared
     *  {@code invariant_violation} code. The catalog carries no entry for it, and the reader is owed
     *  what the decoder wrote rather than the code's name. */
    @Test
    void aRuleWithNoConstraintNamesItsTypeAndClause() throws Exception {
        String en = rendered("named.sou", """
                module named

                data T = Int
                    invariant nonzero = value /= 0

                behavior echo : (a: T) -> T

                let echo (a) = a
                """, "0", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertFalse(en.contains("validation failed"), en);
        assertTrue(en.contains("named.T"), "the rejecting type: " + en);
        assertTrue(en.contains("nonzero"), "the clause that failed: " + en);
    }

    /** A clause declared without a name has no name to report, and says so by leaving it out rather
     *  than by losing the type as well. */
    @Test
    void anUnnamedRuleStillNamesItsType() throws Exception {
        String en = rendered("unnamed.sou", """
                module unnamed

                data T = Int
                    invariant value /= 0

                behavior echo : (a: T) -> T

                let echo (a) = a
                """, "0", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertTrue(en.contains("unnamed.T"), en);
    }

    // --- what the runner relies on the catalog for ---

    /** An entry that needs no metadata applies to every issue carrying its code, and is what makes
     *  the reader's language reach the decoder's wording at all. */
    @Test
    void anEntryThatNeedsNoMetadataStillLocalizes() throws Exception {
        String ja = rendered("tally.sou", """
                data Item = { name: String, price: Int }
                data Out = { n: Int }
                behavior tally : (items: List<Item>) -> Out constructs Out
                let tally (items) = Out { n = List.fold((a, x) -> a + x.price, 0, items) }
                """, "[{\"name\":\"a\"}]", Locale.JAPANESE);
        namesNoPlaceholder(ja);
        assertTrue(ja.contains("必須です"), ja);
    }

    /** The constraint an issue names is what the entry is chosen by, so a lower bound is not
     *  described by the two-sided wording its code also covers. */
    @Test
    void anEntryIsChosenByTheConstraintNotOnlyByTheCode() {
        Issues issues = new Issues(List.of(
                Issue.of(net.unit8.raoh.Path.ROOT.append("age"), "out_of_range",
                        MessageKeys.OUT_OF_RANGE_MINIMUM, "must be at least 0", Map.of("min", 0))));

        String message = issues.resolve(CATALOG, Locale.JAPANESE).asList().get(0).message();
        namesNoPlaceholder(message);
        assertTrue(message.contains("0") && message.contains("以上"), message);
        assertFalse(message.contains("以下"), "no upper bound was stated: " + message);
    }

    /** A code whose entry the metadata cannot fill, and which names no constraint of its own, is
     *  left as the decoder wrote it. */
    @Test
    void anEntryMissingAPlaceholderLeavesTheMessageAlone() {
        Issues issues = new Issues(List.of(
                Issue.of(net.unit8.raoh.Path.ROOT.append("age"), "out_of_range", "must be at least 0",
                        Map.of("min", 0))));

        assertEquals("must be at least 0",
                issues.resolve(CATALOG, Locale.JAPANESE).asList().get(0).message());
    }

    /** A message the decoder marked as its caller's own is not the catalog's to replace, which is
     *  what {@code customMessage} says. */
    @Test
    void aCustomMessageIsNeverReplaced() {
        Issues issues = new Issues(List.of(
                Issue.of(net.unit8.raoh.Path.ROOT, "required", "is required")
                        .withCustomMessage("お名前を入れてください")));

        assertEquals("お名前を入れてください",
                issues.resolve(CATALOG, Locale.JAPANESE).asList().get(0).message());
    }
}
