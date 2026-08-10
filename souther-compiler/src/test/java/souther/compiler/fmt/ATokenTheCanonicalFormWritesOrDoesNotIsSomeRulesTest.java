package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The canonical form's code tokens are a decision too, and a source that wrote others is told which.
 *
 * <p>Three of them, and {@link ACanonicalFormCanRewriteCodeTokensTest} is where they are written
 * out: a trailing comma is dropped, the bar in front of a match's first arm is written, and a
 * definition whose body is a lambda is written with its parameters on the left. Until they were
 * decisions, a source that wrote any of them had a report with nothing in it at all — the rules that
 * hold the two token streams side by side cannot pair them, so they refuse, and the deviations that
 * had nothing to do with the tokens went unsaid with them.
 *
 * <p>They come first in the order the rules depend on each other. What a layout rule answers about is
 * a boundary between two tokens, and which tokens those are is what these settle.
 */
class ATokenTheCanonicalFormWritesOrDoesNotIsSomeRulesTest {

    /**
     * The sites are the ones already written out, which is where the domain comes from.
     *
     * <p>{@link ACanonicalFormCanRewriteCodeTokensTest} has one row per construct the grammar
     * admits a trailing comma in — every loop in the parser that reads a comma — with the bar and
     * the two lambda forms beside them. Building the candidates here again would be a second list
     * of the same thing, and the one that went stale would be this one.
     */
    static Stream<ACanonicalFormCanRewriteCodeTokensTest.Rewrite> rewrites() {
        return ACanonicalFormCanRewriteCodeTokensTest.rewrites();
    }

    /** What each of the three kinds of change is called where a report names it. */
    private static String ruleFor(String change) {
        return switch (change) {
            case "a token is removed" ->
                    "a comma-separated run is written without a comma after its last member";
            case "a token is added" -> "a match writes every arm with its bar";
            case "the tokens are rewritten" ->
                    "a definition writes its parameters to the left of the `=`";
            default -> throw new AssertionError("no such change: " + change);
        };
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("rewrites")
    void theTokenTheCanonicalFormWritesIsNamed(
            ACanonicalFormCanRewriteCodeTokensTest.Rewrite rewrite) {
        Deviations.Report report = Deviations.of(rewrite.source());

        assertTrue(report.deviations().stream()
                        .anyMatch(d -> d.rule().equals(ruleFor(rewrite.change()))),
                "the rule was not named: " + report.deviations());
        assertTrue(report.whole(), "and what is named is not all of it: " + report.deviations());
    }

    /**
     * And what else the source got wrong is named with it.
     *
     * <p>This is what the refusal cost. A source that writes a lambda on the right of a definition
     * is an ordinary source, and every other rule stopped answering about it — so the report for a
     * file with one rewrite in it and a hundred spacing deviations was empty.
     */
    @Test
    void andWhatElseTheSourceGotWrongIsNamedWithIt() {
        String source = "module m\n\nlet f = (x)  ->  x\n";

        Deviations.Report report = Deviations.of(source);

        assertTrue(report.whole(), "what is named is not all of it: " + report.deviations());
        assertEquals("module m\n\nlet f (x) = x\n", Formatter.format(source));
    }

    /** A source that writes the tokens the canonical form writes has nothing against it. */
    @Test
    void andASourceWithTheSameTokensHasNothingAgainstIt() {
        for (ACanonicalFormCanRewriteCodeTokensTest.Rewrite rewrite : rewrites().toList()) {
            String canonical = Formatter.format(rewrite.source());

            assertEquals(List.of(), Deviations.of(canonical).deviations(),
                    "the canonical form of " + rewrite.name() + " has something against it");
        }
    }
}
