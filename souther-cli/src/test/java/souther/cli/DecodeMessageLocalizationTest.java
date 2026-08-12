package souther.cli;

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
 *
 * <p>The wording is asserted whole rather than by a substring. What broke was a message that named a
 * bound the rule did not have, and a message that names one bound too many contains everything a
 * substring check would look for.
 */
class DecodeMessageLocalizationTest {

    @TempDir
    java.nio.file.Path dir;

    /** The catalog `souther run` reads its issues against. */
    private static final ResourceBundleMessageResolver CATALOG =
            new ResourceBundleMessageResolver("net.unit8.raoh.messages");

    /**
     * A placeholder a catalog template could have written, in the grammar the decoder reads them by
     * ({@code net.unit8.raoh.Placeholders}): a letter or underscore, then letters, digits,
     * underscores, dots or hyphens. Narrower than that and a name the decoder would have filled —
     * {@code {range.min}}, {@code {min-bound}} — reaches the reader with this test still green. The
     * grammar is copied because the class stating it is not public.
     */
    private static final Pattern UNFILLED = Pattern.compile("\\{[A-Za-z_][A-Za-z0-9_.\\-]*}");

    private static void namesNoPlaceholder(String rendered) {
        Matcher m = UNFILLED.matcher(rendered);
        assertFalse(m.find(), "a placeholder reached the reader: " + rendered);
    }

    /** The failure of running {@code source} against {@code input}, which each locale then renders. */
    private Runner.RunException failure(String fileName, String source, String input) {
        return assertThrows(Runner.RunException.class, () -> {
            java.nio.file.Path file = dir.resolve(fileName);
            Files.writeString(file, source);
            Runner.run(file, null, input);
        });
    }

    /**
     * What the failure says about the value, in {@code locale} — the runner's own wording around it
     * dropped. Every reason a test reads passes the placeholder sweep on the way through, so no case
     * has to remember to ask for it.
     */
    private static String reason(Runner.RunException e, Locale locale) {
        String rendered = e.localized(locale);
        namesNoPlaceholder(rendered);
        int start = rendered.indexOf("(root): ");
        assertTrue(start >= 0, "the decode detail is missing from: " + rendered);
        return rendered.substring(start + "(root): ".length());
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
    void aLowerBoundOnlyStatesThatBoundAndNoOther() {
        Runner.RunException e =
                failure("ge0.sou", intBounded("ge0", "value >= 0"), "-1");

        assertEquals("must be non-negative", reason(e, Locale.ENGLISH));
        assertEquals("0以上で入力してください", reason(e, Locale.JAPANESE));
    }

    @Test
    void aLowerBoundAwayFromZeroStatesItsNumberAndNoOther() {
        Runner.RunException e =
                failure("ge5.sou", intBounded("ge5", "value >= 5"), "4");

        assertEquals("must be at least 5", reason(e, Locale.ENGLISH));
        assertEquals("5以上で入力してください", reason(e, Locale.JAPANESE));
    }

    @Test
    void anUpperBoundOnlyStatesThatBoundAndNoOther() {
        Runner.RunException e =
                failure("le100.sou", intBounded("le100", "value <= 100"), "101");

        assertEquals("must be at most 100", reason(e, Locale.ENGLISH));
        assertEquals("100以下で入力してください", reason(e, Locale.JAPANESE));
    }

    /** An invariant written with {@code &&} is two constraints, each stating one side. Whichever one
     *  the value breaks reports alone, so neither failure may name the end the other one holds — the
     *  two-sided wording the code also covers would name both. */
    @Test
    void aTwoSidedInvariantReportsWhicheverSideBrokeAndOnlyThat() {
        String source = intBounded("both", "value >= 0 && value <= 100");
        Runner.RunException low = failure("both.sou", source, "-1");
        Runner.RunException high = failure("both.sou", source, "101");

        assertEquals("must be non-negative", reason(low, Locale.ENGLISH));
        assertEquals("0以上で入力してください", reason(low, Locale.JAPANESE));

        assertEquals("must be at most 100", reason(high, Locale.ENGLISH));
        assertEquals("100以下で入力してください", reason(high, Locale.JAPANESE));
    }

    // --- a bound whose strictness the metadata cannot carry ---

    /** A Decimal bound reaches the same constraints as an Int one, and the same catalog entries. */
    @Test
    void anInclusiveDecimalBoundIsStatedAsInclusive() {
        Runner.RunException e =
                failure("dge.sou", decimalBounded("dge", "value >= 0.0m"), "-1.0");

        assertEquals("must be non-negative", reason(e, Locale.ENGLISH));
        assertEquals("0以上で入力してください", reason(e, Locale.JAPANESE));
    }

    /** {@code > 0} rejects 0 and {@code >= 0} admits it, yet both carry {@code min = 0} and nothing
     *  else. What tells them apart is the constraint each issue names, so each has to read as the
     *  rule it is — not merely differently from the other, which a swapped pair would satisfy too. */
    @Test
    void aStrictDecimalBoundIsStatedAsStrict() {
        Runner.RunException e =
                failure("dgt.sou", decimalBounded("dgt", "value > 0.0m"), "0.0");

        assertEquals("must be positive", reason(e, Locale.ENGLISH));
        assertEquals("正の値で入力してください", reason(e, Locale.JAPANESE));
    }

    /** An empty list is rejected as empty rather than as one element short of a bound, which is what
     *  the constraint the mapping chose actually says. */
    @Test
    void anEmptyListIsStatedAsEmptiness() {
        Runner.RunException e = failure("lne.sou", """
                module lne

                data T = List<Int>
                    invariant List.length(value) >= 1

                behavior echo : (a: T) -> T

                let echo (a) = a
                """, "[]");

        assertEquals("must not be empty", reason(e, Locale.ENGLISH));
        assertEquals("空にはできません", reason(e, Locale.JAPANESE));
    }

    // --- a rule no constraint states ---

    /** A clause the mapping cannot prove equivalent keeps its own check and reports the shared
     *  {@code invariant_violation} code. The catalog carries no entry for it, and the reader is owed
     *  what the decoder wrote rather than the code's name. */
    @Test
    void aRuleWithNoConstraintNamesItsTypeAndClause() {
        Runner.RunException e = failure("named.sou", """
                module named

                data T = Int
                    invariant nonzero = value /= 0

                behavior echo : (a: T) -> T

                let echo (a) = a
                """, "0");

        assertEquals("invariant violated on named.T: nonzero", reason(e, Locale.ENGLISH));
        assertEquals("invariant violated on named.T: nonzero", reason(e, Locale.JAPANESE));
    }

    /** A clause declared without a name has no name to report, and says so by leaving it out rather
     *  than by losing the type as well. */
    @Test
    void anUnnamedRuleStillNamesItsType() {
        Runner.RunException e = failure("unnamed.sou", """
                module unnamed

                data T = Int
                    invariant value /= 0

                behavior echo : (a: T) -> T

                let echo (a) = a
                """, "0");

        assertEquals("invariant violated on unnamed.T", reason(e, Locale.ENGLISH));
    }

    // --- what the runner relies on the catalog for ---

    /** An entry that needs no metadata applies to every issue carrying its code, and is what makes
     *  the reader's language reach the decoder's wording at all. */
    @Test
    void anEntryThatNeedsNoMetadataStillLocalizes() {
        Runner.RunException e = failure("tally.sou", """
                data Item = { name: String, price: Int }
                data Out = { n: Int }
                behavior tally : (items: List<Item>) -> Out constructs Out
                let tally (items) = Out { n = List.fold((a, x) -> a + x.price, 0, items) }
                """, "[{\"name\":\"a\"}]");

        String ja = e.localized(Locale.JAPANESE);
        namesNoPlaceholder(ja);
        assertTrue(ja.contains("/0/price: 必須です"), ja);
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
        assertEquals("0以上で入力してください", message);
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
