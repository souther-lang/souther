package souther.compiler.diag;

import java.util.Locale;

/**
 * The public identity of a compiler diagnostic.
 *
 * <p>A code names one normative rule of the language — not one message template and not one title
 * category. The rule is identified by {@link #ruleAnchor()}, an anchor in the specification, and no
 * two codes share one: two diagnostics carry the same code exactly when they report the same rule
 * broken in different ways, and different codes when they enforce different rules, however alike
 * their titles or their sections read.
 *
 * <p>The three names a diagnostic carries are separate on purpose:
 *
 * <ul>
 *   <li>{@link #titleKey()} is the category a reader sees in the header — {@code BOUNDARY TYPE},
 *       {@code TYPE MISMATCH}. It is shared, and says nothing about identity;</li>
 *   <li>this code is the identity a reader looks up and a tool keys on;</li>
 *   <li>the message key a site passes to {@link Diagnostic#of} is the wording for one way the rule
 *       was broken, and several of them belong to one code.</li>
 * </ul>
 *
 * <p>A retired code is not here — it is in {@link RetiredDiagnosticCode}, so that what a compile can
 * emit and what a number once meant are two lists and a number is never reused.
 */
public enum DiagnosticCode {

    // --- declarations: construction authority, fields, invariants, matching ---
    E1002("constructs-authority-complete", "e1002.title"),
    E1004("spread-fields-do-not-collide", "e1004.title"),
    E1005("construction-supplies-every-field", "e1005.title"),
    E1006("constructs-no-overdeclaration", "e1006.title"),
    E1007("newtype-wraps-an-external-representation", "parse.title"),
    E1008("unit-data-is-written-without-a-body", "check.data.invalid.title"),
    E1101("invariant-expression-is-bool", "e1101.title"),
    E1102("invariant-needs-a-value-to-constrain", "check.invariant.invalid.title"),
    E1103("invariant-clause-names-are-distinct", "check.invariant.invalid.title"),
    E1104("invariant-clause-name-is-not-underscore", "check.invariant.invalid.title"),
    E1201("match-covers-every-case", "e1201.title"),

    // --- what the language does not have ---
    E1301("no-null", "e1301.title"),
    E1303("option-cases-are-not-written", "e1303.title"),
    E1305("injected-constructs-are-creatable", "e1305.title"),
    E1307("unreachable-stands-where-a-type-is-stated", "check.type.mismatch.title"),
    E1308("optional-marks-one-type", "parse.title"),
    E1310("unreachable-states-its-reason", "parse.title"),
    E1401("no-arbitrary-jvm-calls", "e1401.title"),
    E1402("core-privileges-stay-in-the-core", "parse.title"),

    // --- modules, requirements, composition ---
    E1501("module-dependencies-are-acyclic", "e1501.title"),
    E1502("a-core-name-is-not-taken", "check.module.title"),
    E1503("a-module-is-declared-in-one-place", "check.module.title"),
    E1504("every-module-reached-is-on-the-path", "check.module.title"),
    E1505("a-published-module-agrees-with-this-compiler", "check.module.title"),
    E1506("a-reached-name-is-declared-by-its-module", "check.module.title"),
    E1507("a-reached-name-is-exposed-by-its-module", "check.module.title"),
    E1508("an-imported-name-denotes-one-thing", "check.module.title"),
    E1602("depends-on-names-every-requirement", "e1602.title"),
    E1603("depends-on-names-no-more", "e1603.title"),
    E1604("composition-output-agrees-with-inference", "e1604.title"),
    E1605("exposed-composition-declares-its-output", "e1605.title"),
    E1606("sum-cases-are-declared-with-the-sum", "check.sum.title"),
    E1607("depends-on-names-a-dependency", "e1607.title"),
    E1608("behavior-does-not-reach-itself", "e1608.title"),
    E1609("exposing-lists-this-modules-own-definitions", "check.module.title"),
    E1610("exposing-is-type-granular", "check.module.title"),
    E1611("an-exposed-signature-names-only-exposed-types", "check.module.title"),
    E1612("an-injection-target-declares-no-depends-on", "check.module.title"),
    E1701("composition-stages-type-route", "e1701.title"),

    // --- examples ---
    E1901("example-target-is-a-behavior", "check.example.title"),
    E1902("example-target-is-evaluable", "check.example.title"),
    E1903("example-fixtures-are-buildable", "check.example.title"),
    E1904("example-expected-arm-is-an-output-case", "check.example.title"),
    E1905("example-holds", "check.example.title"),
    E1906("examples-file-holds-only-examples", "check.example.title"),
    E1907("examples-file-names-a-compiled-module", "check.example.title"),
    E1908("example-dependency-has-a-usable-fake", "check.example.title"),
    E1909("fake-answers-the-inputs-it-is-asked", "check.example.title"),
    E1910("example-evaluation-stays-within-budget", "check.example.title"),
    E1911("example-does-not-reach-unreachable", "check.example.title"),
    E1913("every-output-case-is-expected-by-a-row", "check.example.title"),
    E1915("every-input-case-is-used-by-a-row", "check.example.title"),
    E1916("every-guard-boundary-has-a-row", "check.example.title"),
    E1918("every-arm-has-a-row", "check.example.title"),
    E1919("stand-in-and-recorded-row-agree", "check.example.title"),
    E1920("stand-in-comparison-completes", "check.example.title"),
    E1921("fake-table-builds", "check.example.title"),
    E1922("imports-are-used", "check.import.title"),
    E1923("example-evaluation-answers", "check.example.title"),
    E1924("example-evaluation-stays-within-stack", "check.example.title"),

    // --- totality, invariant discharge, attempted construction ---
    E2001("helper-carries-its-termination-guarantee", "check.totality.title"),
    E2010("construction-satisfies-its-invariant", "check.invariant.title"),
    E2011("construction-invariant-is-discharged", "check.invariant.title"),
    E2012("attempt-subject-is-a-construction", "check.attempt.title"),
    E2013("attempt-subject-declares-an-invariant", "check.attempt.title"),
    E2014("attempt-arm-names-a-declared-clause", "check.attempt.title"),
    E2015("attempt-answers-every-failing-clause", "check.attempt.title"),
    E2016("attempt-answers-unnamed-clauses", "check.attempt.title"),
    E2017("attempt-catch-all-has-clauses-to-answer", "check.attempt.title"),
    E2018("attempt-arms-answer-an-attempt", "check.attempt.title"),
    E2019("attempt-answers-each-clause-once", "check.attempt.title"),

    // --- what the JVM will hold, and what the compiler will walk ---
    E2101("generated-methods-fit-jvm-parameter-slots", "e2101.title"),
    E2102("generated-methods-fit-jvm-code-size", "e2102.title"),
    E2103("generated-classes-fit-jvm-constant-pool", "e2103.title"),
    E2104("source-nesting-is-bounded", "e2104.title"),

    // --- the text as written ---
    E2301("declaration-syntax", "parse.title"),
    E2302("expression-syntax", "parse.title"),
    E2303("pattern-syntax", "parse.title"),
    E2304("examples-syntax", "parse.title"),
    E2305("literal-syntax", "parse.title");

    private final String ruleAnchor;
    private final String titleKey;

    DiagnosticCode(String ruleAnchor, String titleKey) {
        this.ruleAnchor = ruleAnchor;
        this.titleKey = titleKey;
    }

    /** The specification anchor of the rule this code reports broken. Unique across the codes. */
    public String ruleAnchor() {
        return ruleAnchor;
    }

    /** The catalog key of the header category this code is shown under. Shared across codes. */
    public String titleKey() {
        return titleKey;
    }

    /** The anchor of this code's own section, which {@code souther doc} answers from. */
    public String docAnchor() {
        return name().toLowerCase(Locale.ROOT);
    }
}
