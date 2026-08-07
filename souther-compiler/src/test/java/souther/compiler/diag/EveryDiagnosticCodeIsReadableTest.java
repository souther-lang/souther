package souther.compiler.diag;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a diagnostic code is, held as an invariant rather than as a convention.
 *
 * <p>A code is the public identity of a compiler diagnostic — {@code souther doc e1918} is the
 * affordance the toolchain advertises, and the JSON and LSP paths key on the same string. Three
 * things have to hold for that to mean anything, and each is a test here: a code names exactly one
 * rule, a code resolves to documentation, and documentation names no code that is not one.
 *
 * <p>The rule anchor is what makes the first checkable. Two diagnostics carry one code when they
 * report one rule broken in different ways, and two codes when they enforce different rules — so
 * the anchors are distinct, and picking an anchor another code already claims is either a sign the
 * two are one rule (share the code) or that a new rule wants stating (write it, and anchor it).
 */
class EveryDiagnosticCodeIsReadableTest {

    private static final String SPEC = "/META-INF/souther/specification.adoc";
    private static final String CATALOG = "/souther/compiler/diag/messages.properties";

    /** {@code [#anchor]} on its own line — a section's, or a normative paragraph's. */
    private static final Pattern BLOCK_ANCHOR = Pattern.compile("(?m)^\\[#([a-z0-9-]+)]$");
    /** {@code [[anchor]]} inline — a normative list item's. */
    private static final Pattern INLINE_ANCHOR = Pattern.compile("\\[\\[([a-z0-9-]+)]]");
    /** A section anchor named for a code: the answer {@code souther doc <code>} gives. */
    private static final Pattern CODE_SECTION =
            Pattern.compile("(?m)^\\[#(e[0-9]{4})(-removed)?]\\r?\\n=");

    @Test
    void everyCodeNamesARuleTheSpecificationStates() throws IOException {
        Set<String> anchors = anchorsOf(spec());
        Set<String> missing = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (!anchors.contains(code.ruleAnchor())) {
                missing.add(code + " -> " + code.ruleAnchor());
            }
        }
        assertEquals(Set.of(), missing,
                "a code names a rule anchor the specification does not carry");
    }

    /**
     * No two codes name one rule. This is the check that keeps the codes at the granularity of the
     * language's obligations: a second code for a rule that already has one, or one code stretched
     * over two rules, shows up here rather than as an author being told to look up a section that
     * describes something else.
     */
    @Test
    void noTwoCodesNameTheSameRule() {
        Set<String> seen = new LinkedHashSet<>();
        List<String> shared = new ArrayList<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (!seen.add(code.ruleAnchor())) {
                shared.add(code + " -> " + code.ruleAnchor());
            }
        }
        assertEquals(List.of(), shared, "two codes claim one rule");
    }

    @Test
    void everyCodeResolvesToASection() throws IOException {
        Set<String> sections = codeSectionsOf(spec(), false);
        Set<String> missing = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (!sections.contains(code.docAnchor())) {
                missing.add(code.name());
            }
        }
        assertEquals(Set.of(), missing,
                "`souther doc <code>` has no answer for these — a reader who meets one has nothing to type");
    }

    @Test
    void everyRetiredCodeResolvesToItsRetirementNote() throws IOException {
        Set<String> retiredSections = codeSectionsOf(spec(), true);
        Set<String> missing = new TreeSet<>();
        for (RetiredDiagnosticCode code : RetiredDiagnosticCode.values()) {
            if (!retiredSections.contains(code.docAnchor())) {
                missing.add(code.name());
            }
        }
        assertEquals(Set.of(), missing, "a retired code says nothing about what replaced it");
    }

    /**
     * The other direction. Without it a code deleted from the compiler leaves its section behind,
     * and the specification keeps answering for something no compile can emit.
     */
    @Test
    void everySectionNamedForACodeNamesOneThatExists() throws IOException {
        String spec = spec();
        Set<String> live = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            live.add(code.docAnchor());
        }
        Set<String> retired = new TreeSet<>();
        for (RetiredDiagnosticCode code : RetiredDiagnosticCode.values()) {
            retired.add(code.docAnchor());
        }
        assertEquals(Set.of(), difference(codeSectionsOf(spec, false), live),
                "a section is named for a code no compile emits; retire it as `[#eNNNN-removed]`");
        assertEquals(Set.of(), difference(codeSectionsOf(spec, true), retired),
                "a retirement note names a number that is not on the retired list");
    }

    /**
     * A number means one thing forever. The two lists being disjoint is what stops a retired code
     * from coming back for a different rule, which would make every record of the old one wrong.
     */
    @Test
    void noNumberIsBothLiveAndRetired() {
        Set<String> live = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            live.add(code.name());
        }
        Set<String> reused = new TreeSet<>();
        for (RetiredDiagnosticCode code : RetiredDiagnosticCode.values()) {
            if (live.contains(code.name())) {
                reused.add(code.name());
            }
        }
        assertEquals(Set.of(), reused, "a retired number is being emitted again");
    }

    /** A code carries the title it is shown under, so the catalog has to define it. */
    @Test
    void everyCodeCarriesATitleTheCatalogDefines() throws IOException {
        Properties catalog = new Properties();
        try (InputStream in = EveryDiagnosticCodeIsReadableTest.class.getResourceAsStream(CATALOG)) {
            catalog.load(new java.io.InputStreamReader(in, StandardCharsets.UTF_8));
        }
        Set<String> missing = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (!catalog.containsKey(code.titleKey())) {
                missing.add(code + " -> " + code.titleKey());
            }
        }
        assertEquals(Set.of(), missing, "a code is shown under a title nothing defines");
    }

    /**
     * The migration, held to a number that only goes down.
     *
     * <p>{@link Diagnostic#uncoded} is what a site reaches for when its diagnostic has not been
     * mapped onto a rule yet: it renders a title and nothing a reader can look up. There is no
     * reason to add one — a new diagnostic reports a rule, and a rule has an anchor and a code — so
     * the count is a ceiling, and this test is what stops the set from growing back while it is
     * being emptied.
     */
    @Test
    void theUncodedSitesOnlyGoDown() throws IOException {
        int remaining = 0;
        for (java.nio.file.Path source : MessageCatalogFormatTest.mainSources()) {
            Matcher m = Pattern.compile("\\.uncoded\\(")
                    .matcher(java.nio.file.Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                remaining++;
            }
        }
        assertFalse(remaining == 0 && UNCODED_CEILING > 0,
                "no uncoded site is left — drop this test and `Diagnostic.uncoded` with it");
        assertTrue(remaining <= UNCODED_CEILING,
                "an uncoded diagnostic was added: " + remaining + " of them, and the ceiling is "
                        + UNCODED_CEILING + ". A new diagnostic reports a rule, so give it a rule "
                        + "anchor and a DiagnosticCode.");
        assertEquals(UNCODED_CEILING, remaining,
                "uncoded sites were removed — lower the ceiling to " + remaining + " so they cannot come back");
    }

    /** How many diagnostics are still unmapped. Lower it as they are mapped; never raise it. */
    private static final int UNCODED_CEILING = 82;

    private static String spec() throws IOException {
        try (InputStream in = EveryDiagnosticCodeIsReadableTest.class.getResourceAsStream(SPEC)) {
            if (in == null) {
                throw new IllegalStateException("the bundled specification is missing: " + SPEC);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
    }

    private static Set<String> anchorsOf(String adoc) {
        Set<String> anchors = new TreeSet<>();
        for (Pattern p : List.of(BLOCK_ANCHOR, INLINE_ANCHOR)) {
            Matcher m = p.matcher(adoc);
            while (m.find()) {
                anchors.add(m.group(1));
            }
        }
        return anchors;
    }

    /** The {@code [#eNNNN]} sections, or the {@code [#eNNNN-removed]} ones. */
    private static Set<String> codeSectionsOf(String adoc, boolean retired) {
        Set<String> found = new TreeSet<>();
        Matcher m = CODE_SECTION.matcher(adoc);
        while (m.find()) {
            if ((m.group(2) != null) == retired) {
                found.add(m.group(1) + (retired ? "-removed" : ""));
            }
        }
        return found;
    }

    private static Set<String> difference(Set<String> from, Set<String> without) {
        Set<String> left = new TreeSet<>(from);
        left.removeAll(without);
        return left;
    }

    static {
        // The anchors are matched case-sensitively against a lower-cased code name; a code declared
        // in any other case would silently never match.
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (!code.name().equals(code.name().toUpperCase(Locale.ROOT))) {
                throw new IllegalStateException("a code is not upper case: " + code);
            }
        }
    }
}
