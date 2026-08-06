package souther.compiler;

import net.unit8.raoh.Issue;
import net.unit8.raoh.Issues;

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
 * What a decode failure says once the catalog has had its turn. The decoder writes every issue a
 * message of its own and marks it replaceable, so a catalog entry can say the same thing in the
 * reader's language. Replacing it is only an improvement where the entry says as much: a template
 * whose placeholders the issue's metadata cannot fill states a bound that is not there
 * ({@code must be between 0 and {max}}), and a code the catalog does not carry at all resolves to the
 * code itself ({@code validation failed: invariant_violation}). Neither is worth what it replaced,
 * so the issue's own message stands (issues #365, #371).
 */
class DecodeMessageLocalizationTest {

    @TempDir
    java.nio.file.Path dir;

    private java.nio.file.Path write(String fileName, String source) throws Exception {
        java.nio.file.Path file = dir.resolve(fileName);
        Files.writeString(file, source);
        return file;
    }

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

    /** The catalog cannot state a one-sided bound, so the reader gets the decoder's own English
     *  rather than a Japanese sentence naming a bound that is not there. Being in the wrong language
     *  is a smaller loss than being wrong. */
    @Test
    void aOneSidedBoundKeepsItsMeaningInEveryLocale() throws Exception {
        String ja = rendered("ge0ja.sou", intBounded("ge0ja", "value >= 0"), "-1", Locale.JAPANESE);
        namesNoPlaceholder(ja);
        assertFalse(ja.contains("以下"), "no upper bound is stated by `value >= 0`: " + ja);
    }

    /** A Decimal bound reaches the same constraints as an Int one, and the same catalog entry. */
    @Test
    void aDecimalBoundNamesTheBoundItStates() throws Exception {
        String en = rendered("dge.sou", decimalBounded("dge", "value >= 0.0m"), "-1.0", Locale.ENGLISH);
        namesNoPlaceholder(en);
        assertTrue(en.contains("must be non-negative"), en);
    }

    /** {@code > 0} and {@code >= 0} admit different values, so they cannot read alike. Both carry
     *  {@code min = 0} in the metadata, which is why a catalog keyed on that alone cannot tell them
     *  apart. */
    @Test
    void aStrictDecimalBoundReadsDifferentlyFromAnInclusiveOne() throws Exception {
        String strict = rendered("dgt.sou", decimalBounded("dgt", "value > 0.0m"), "0.0",
                Locale.ENGLISH);
        String inclusive = rendered("dge2.sou", decimalBounded("dge2", "value >= 0.0m"), "-1.0",
                Locale.ENGLISH);
        namesNoPlaceholder(strict);
        namesNoPlaceholder(inclusive);
        assertFalse(strict.contains(inclusive.substring(inclusive.indexOf("must be"))),
                "a rule that rejects 0 cannot read as one that admits it: " + strict);
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

    // --- what the catalog still gets to say ---

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

    /** An entry whose placeholders the metadata fills is the case the catalog was written for, and
     *  keeps working — the guard is about applicability, not about refusing the catalog. */
    @Test
    void anEntryWhosePlaceholdersAreAllFilledIsUsed() {
        Issues issues = new Issues(List.of(
                Issue.of(net.unit8.raoh.Path.ROOT.append("age"), "out_of_range", "out of range",
                        Map.of("min", 0, "max", 150))));

        String message = DecodeMessages.localize(issues, Locale.JAPANESE).asList().get(0).message();
        namesNoPlaceholder(message);
        assertTrue(message.contains("0") && message.contains("150"), message);
        assertTrue(message.contains("入力してください"), "the reader's language, not the decoder's: " + message);
    }

    /** The same entry, one placeholder short: the template states an upper bound the issue never
     *  claimed, so it does not apply and the decoder's own message stands. */
    @Test
    void anEntryMissingAPlaceholderLeavesTheMessageAlone() {
        Issues issues = new Issues(List.of(
                Issue.of(net.unit8.raoh.Path.ROOT.append("age"), "out_of_range", "must be at least 0",
                        Map.of("min", 0))));

        assertEquals("must be at least 0",
                DecodeMessages.localize(issues, Locale.JAPANESE).asList().get(0).message());
    }

    /** A message the decoder marked as its caller's own is not the catalog's to replace, which is
     *  what {@code customMessage} says. */
    @Test
    void aCustomMessageIsNeverReplaced() {
        Issues issues = new Issues(List.of(
                Issue.of(net.unit8.raoh.Path.ROOT, "required", "is required")
                        .withCustomMessage("お名前を入れてください")));

        assertEquals("お名前を入れてください",
                DecodeMessages.localize(issues, Locale.JAPANESE).asList().get(0).message());
    }
}
