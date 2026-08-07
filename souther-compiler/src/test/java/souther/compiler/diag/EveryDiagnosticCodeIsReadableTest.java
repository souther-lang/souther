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

/**
 * What a diagnostic code is, held as an invariant rather than as a convention.
 *
 * <p>A code is the public identity of a compiler diagnostic — {@code souther doc e1918} is the
 * affordance the toolchain advertises, and the JSON and LSP paths key on the same string. Three
 * things have to hold for that to mean anything, and each is a test here: a code names exactly one
 * rule, a code resolves to documentation, and documentation names no code that is not one.
 *
 * <p>That a code resolves is checked next door, in {@code
 * EveryDiagnosticTheCompilerEmitsCanBeLookedUpTest}, which asks the document rather than the text.
 * What is here is the other direction and the rule anchors.
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
     * The way back is closed. A check that refuses a program raises a {@link Diagnostic} through
     * {@link Diagnostic#of}, which takes a {@link DiagnosticCode} — there is no builder that does
     * not, so a diagnostic a reader cannot look up cannot be written.
     *
     * <p>{@link Diagnostic#literal} is the exception and is not a check raising one: it wraps a
     * message the compiler was handed — a failure surfacing as a report — where there is no rule to
     * name because nothing decided the program was wrong. Held to the one site that does that, so the next `+literal+` in a checker is a
     * failing test rather than a diagnostic quietly losing its identity again.
     */
    @Test
    void nothingRaisesADiagnosticWithoutACode() throws IOException {
        List<String> raising = new ArrayList<>();
        for (java.nio.file.Path source : MessageCatalogFormatTest.mainSources()) {
            String text = java.nio.file.Files.readString(source, StandardCharsets.UTF_8);
            Matcher m = Pattern.compile("Diagnostic\\.literal\\(").matcher(text);
            while (m.find()) {
                raising.add(source.toString().replace('\\', '/')
                        .replaceAll(".*/src/main/java/", ""));
            }
        }
        assertEquals(List.of("souther/compiler/query/Report.java"), raising,
                "a diagnostic was raised with no code; a check reports a rule, so name the rule and"
                        + " give it a DiagnosticCode. One site wraps a message the compiler was"
                        + " handed, and one is all there is room for");
    }

    /**
     * A code on the live list is one the compiler still names.
     *
     * <p>The other direction of the documentation checks: those hold that every code resolves, and
     * would go on holding after the site that names one is deleted, leaving an enum constant and a
     * section for something no reader can ever meet. Retired codes are kept apart so that the live
     * list means something, and this is what keeps it from filling with numbers nothing reaches.
     *
     * <p>What it proves is that the name is written somewhere outside the enum, and not that a
     * compile can print it: a comparison or a piece of dispatch naming the code would satisfy this
     * with the emission site gone. Proving the stronger thing takes an input that produces the
     * diagnostic, which is what the per-code tests do where the code is worth one — the five syntax
     * rules have such a test each, since those were assigned by a helper that could not see its own
     * context.
     */
    @Test
    void everyCodeIsNamedByCompilerSource() throws IOException {
        Set<String> referenced = new TreeSet<>();
        Pattern named = Pattern.compile("DiagnosticCode\\.(E[0-9]{4})");
        for (java.nio.file.Path source : MessageCatalogFormatTest.mainSources()) {
            if (source.getFileName().toString().equals("DiagnosticCode.java")) {
                continue;   // the declaration is not a use
            }
            Matcher m = named.matcher(java.nio.file.Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                referenced.add(m.group(1));
            }
        }
        Set<String> unemitted = new TreeSet<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            if (!referenced.contains(code.name())) {
                unemitted.add(code.name());
            }
        }
        assertEquals(Set.of(), unemitted,
                "these are on the live list and nothing names them; retire them or emit them");
    }

    /**
     * A message key that names a code is emitted under that code.
     *
     * <p>Most keys are named for what they say. Some are named for a code — {@code e1607.unknown} —
     * and those carry an assertion in their spelling, which goes stale the moment the diagnostic is
     * found to report a different rule than the one it was first filed under. Two did: a data
     * declaring a field twice was reported as a spread collision, and a behavior called from a
     * helper as an arbitrary Java call. Both read correctly at the site and wrongly at the key.
     *
     * <p>This is the one part of "the site reports the rule its code names" a machine can check.
     * The rest is read, and was.
     */
    @Test
    void aKeyNamedForACodeIsEmittedUnderIt() throws IOException {
        Pattern emission = Pattern.compile(
                "DiagnosticCode\\.(E[0-9]{4})\\s*,\\s*\\n?\\s*(?:[^;]{0,160}?)\"(e([0-9]{4})\\.[a-z.]+)\"");
        List<String> disagreeing = new ArrayList<>();
        for (java.nio.file.Path source : MessageCatalogFormatTest.mainSources()) {
            Matcher m = emission.matcher(
                    java.nio.file.Files.readString(source, StandardCharsets.UTF_8));
            while (m.find()) {
                if (!m.group(1).equals("E" + m.group(3))) {
                    disagreeing.add(m.group(2) + " emitted as " + m.group(1));
                }
            }
        }
        assertEquals(List.of(), disagreeing,
                "a key naming one code is emitted under another; rename the key for what it says,"
                        + " or move the site to the code its rule has");
    }

    /**
     * A title named for a code belongs to that code.
     *
     * <p>A title is a category and is shared on purpose — twenty codes read {@code BOUNDARY TYPE} —
     * but a few are named {@code eNNNN.title}, from before there was anything but a code to name
     * them after. Those are not categories, and a second code taking one says a reader is being
     * shown the classification of a rule this is not: E1818 was shown as {@code ARBITRARY JAVA
     * CALL} while its own section said it is not that.
     *
     * <p>Only the borrowing is checkable. A code under a shared title whose wording contradicts its
     * rule — E1816 read {@code TYPE MISMATCH} beside a specification saying it is not one — is read
     * for, as the rules themselves are.
     */
    @Test
    void aTitleNamedForACodeIsUsedByThatCode() {
        List<String> borrowed = new ArrayList<>();
        for (DiagnosticCode code : DiagnosticCode.values()) {
            Matcher m = Pattern.compile("^e([0-9]{4})\\.title$").matcher(code.titleKey());
            if (m.matches() && !code.name().equals("E" + m.group(1))) {
                borrowed.add(code + " -> " + code.titleKey());
            }
        }
        assertEquals(List.of(), borrowed,
                "a code is shown under a title named for another; give it a category of its own");
    }

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
