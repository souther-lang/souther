package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.ValueSet;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position held by a format and by a length rule is read where each of them is read whole by one
 * of the two readings, and is not where one of them is read by neither.
 *
 * <p>The set of values holds the format and has no word for the length, and the bounds hold the
 * length and have no word for the format. Each reading is short of the rules on its own, and the
 * strings both leave are exactly what the rules leave.
 */
class AFormatAndALengthRuleTogetherAreReadTest {

    private static final String FORMAT_AND_LENGTH_IN_ONE_CLAUSE = """
            module bounded

            data Email = String invariant
                String.matches("[^\\\\s]+", value) && String.length(value) <= 254

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String FORMAT_AND_LENGTH_IN_TWO_CLAUSES = """
            module bounded

            data Email = String
                invariant format = String.matches("[^\\\\s]+", value)
                invariant length = String.length(value) <= 254

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String LENGTH_BEFORE_FORMAT = """
            module bounded

            data Email = String
                invariant length = String.length(value) <= 254
                invariant format = String.matches("[^\\\\s]+", value)

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String FORMAT_WRITTEN_AS_ONE_PATTERN = """
            module bounded

            data Email = String invariant String.matches("[^\\\\s]{1,254}", value)

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String FORMAT_OR_LENGTH = """
            module bounded

            data Email = String invariant
                String.matches("[^\\\\s]+", value) || String.length(value) <= 254

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String LENGTH_WITH_A_HOLE = """
            module bounded

            data Email = String invariant
                String.matches("a+", value) && String.length(value) /= 2

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String LENGTH_BOUNDED_BY_A_SIBLING = """
            module bounded

            data Pair = { left: String, right: String }
                invariant tied = String.matches("a+", left)
                    && String.length(left) == String.length(right)

            data Ok

            behavior f : (pair: Pair) -> Ok
            """;

    private static final String LENGTH_BESIDE_AN_ORDER = """
            module bounded

            data Email = String invariant
                String.matches("[a-z]+", value) && value >= "m" && String.length(value) <= 5

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String BOTH_RULES_NAMED_AS_ONE_HELPER = """
            module bounded

            let validEmail (s: String) =
                String.matches("[^\\\\s]+", s) && String.length(s) <= 254

            data Email = String invariant validEmail(value)

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static final String A_SIBLING_WITH_RULES_OF_ITS_OWN = """
            module bounded

            data Pair = { email: String, code: String }
                invariant mail = String.matches("[a-z]+", email) && String.length(email) <= 5
                invariant digits = String.matches("[0-9]+", code)

            data Ok

            behavior f : (pair: Pair) -> Ok
            """;

    private static final String A_SIBLING_NOTHING_SATISFIES = """
            module bounded

            data Pair = { email: String, code: String }
                invariant mail = String.matches("[a-z]+", email) && String.length(email) <= 5
                invariant digits = String.matches("[0-9]+", code) && String.matches("[a-z]+", code)

            data Ok

            behavior f : (pair: Pair) -> Ok
            """;

    private static final String A_SIBLING_COMPARED_WITH_THE_POSITION = """
            module bounded

            data Pair = { email: String, code: String }
                invariant mail = String.matches("[a-z]+", email) && String.length(email) <= 5
                invariant same = email /= code

            data Ok

            behavior f : (pair: Pair) -> Ok
            """;

    private static final String A_HELPER_WHOSE_FORMAT_IS_A_CHOICE = """
            module bounded

            let validEmail (s: String) =
                (String.matches("[^\\\\s]+", s) || String.matches("[a-z]+", s))
                    && String.length(s) <= 254

            data Email = String invariant validEmail(value)

            data Ok

            behavior f : (email: Email) -> Ok
            """;

    private static Position positionOf(String source, String parameter, ReadingPolicy policy) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules, policy, TestDay.TODAY);
        return InputDomain.of(sigs.get("f"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none()).positions().stream()
                .filter(p -> p.path().toString().equals(parameter))
                .findFirst().orElseThrow();
    }

    private static AdmissibleSet.Completeness completenessOf(String source, String parameter) {
        return positionOf(source, parameter, ReadAs.THE_COMPILATION_DOES).completeness();
    }

    private static ValueSet admittedOf(String source, String parameter) {
        return positionOf(source, parameter, ReadAs.THE_COMPILATION_DOES)
                .admitted().approximation();
    }

    @Test
    void aFormatAndALengthWrittenInOneClauseAreRead() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(FORMAT_AND_LENGTH_IN_ONE_CLAUSE, "email"));
    }

    @Test
    void andWrittenInTwoClauses() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(FORMAT_AND_LENGTH_IN_TWO_CLAUSES, "email"));
    }

    @Test
    void andInTheOtherOrder() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(LENGTH_BEFORE_FORMAT, "email"));
    }

    /**
     * What the position admits is the strings the rules leave, and the same whichever way the two
     * rules were written.
     *
     * <p>{@code Complete} says the set is exact, so the set is asked: the one the single pattern
     * builds, and the strings either side of each end.
     */
    @Test
    void theSetIsTheStringsTheRulesLeaveWhicheverWayTheyAreWritten() {
        ValueSet onePattern = admittedOf(FORMAT_WRITTEN_AS_ONE_PATTERN, "email");
        assertEquals(onePattern, admittedOf(FORMAT_AND_LENGTH_IN_ONE_CLAUSE, "email"));
        assertEquals(onePattern, admittedOf(FORMAT_AND_LENGTH_IN_TWO_CLAUSES, "email"));
        assertEquals(onePattern, admittedOf(LENGTH_BEFORE_FORMAT, "email"));
        assertEquals(onePattern, admittedOf(BOTH_RULES_NAMED_AS_ONE_HELPER, "email"));

        Language language = assertInstanceOf(ValueSet.Matching.class, onePattern).language();
        assertFalse(language.has(""), "the format wants a character");
        assertFalse(language.has("a b"), "and no space");
        assertTrue(language.has("a".repeat(254)), "the longest the length leaves");
        assertFalse(language.has("a".repeat(255)), "and not one past it");
    }

    /**
     * Where the set met with the count could not be built the position stays short, for the reason
     * that it was not built.
     *
     * <p>The format is a small machine and the count is as many states as it has lengths, so a
     * budget for the first and not the second refuses the meet and nothing else.
     */
    @Test
    void whereTheMeetCannotBeBuiltTheAnswerIsStillTooCostly() {
        PatternPlan.Budget small = new PatternPlan.Budget(16, 64, 1_000_000L);
        ReadingPolicy policy = new ReadingPolicy(ReadAs.THE_COMPILATION_DOES.dnfExpansionLimit(),
                ReadAs.THE_COMPILATION_DOES.scalePlacesLimit(), small, small);
        AdmissibleSet.Completeness read = positionOf(FORMAT_AND_LENGTH_IN_ONE_CLAUSE, "email",
                policy).completeness();

        AdmissibleSet.Completeness.Wider wider =
                assertInstanceOf(AdmissibleSet.Completeness.Wider.class, read);
        assertTrue(wider.why().contains(new AdmissibleSet.Widening.ExactValuesTooCostly()),
                "what was not built is said, and not a rule going unread: " + wider);
    }

    /**
     * A third rule neither reading takes in leaves the position short, whichever way it is short.
     *
     * <p>The format and the length are each read by one of the two, and the third by neither: the
     * set does not hold it and the bounds do not state it. One is a form the set has no word for
     * and the other a call the reading never reached.
     */
    @Test
    void norWhereAThirdRuleIsReadByNeither() {
        for (String third : new String[] {
                "String.startsWith(\"a\", String.trim(value))",
                "String.toUpper(value) == value"}) {
            String model = """
                    module bounded

                    data Email = String invariant
                        String.matches("[^\\\\s]+", value) && String.length(value) <= 254
                            && %s

                    data Ok

                    behavior f : (email: Email) -> Ok
                    """.formatted(third);
            assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                    completenessOf(model, "email"), third);
        }
    }

    @Test
    void andWhereTheHelpersFormatIsAChoiceBetweenTwoPatternsTheSetHoldsWhole() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(A_HELPER_WHOSE_FORMAT_IS_A_CHOICE, "email"));
        assertEquals(admittedOf(FORMAT_WRITTEN_AS_ONE_PATTERN, "email"),
                admittedOf(A_HELPER_WHOSE_FORMAT_IS_A_CHOICE, "email"),
                "the second pattern leaves nothing the first does not");
    }

    @Test
    void norBesideASiblingNoValueSatisfies() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                completenessOf(A_SIBLING_NOTHING_SATISFIES, "pair.email"),
                "no value of the pair exists, and the rules leave this position nothing at all");
    }

    @Test
    void norBesideASiblingTheRulesCompareWithThePosition() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                completenessOf(A_SIBLING_COMPARED_WITH_THE_POSITION, "pair.email"),
                "what the sibling holds changes which strings are left here");
    }

    @Test
    void andNamedAsOneHelperWhoseBodyStatesBoth() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(BOTH_RULES_NAMED_AS_ONE_HELPER, "email"));
    }

    @Test
    void andBesideASiblingWhoseRulesAreItsOwn() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(A_SIBLING_WITH_RULES_OF_ITS_OWN, "pair.email"));
    }

    @Test
    void asTheSameStringsWrittenAsOnePatternAre() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(FORMAT_WRITTEN_AS_ONE_PATTERN, "email"));
    }

    @Test
    void butNotWhereTheFormatIsAChoiceBesideTheLength() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                completenessOf(FORMAT_OR_LENGTH, "email"),
                "a union of the two is not what their intersection leaves");
    }

    @Test
    void norWhereTheBoundsLeaveAHoleTheyDoNotState() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                completenessOf(LENGTH_WITH_A_HOLE, "email"),
                "the bounds are the run of lengths and not the hole in it, so the string of two is"
                        + " one the set and the bounds both leave");
    }

    @Test
    void andWhereAnOrderTheSetHoldsStandsBesideThem() {
        assertInstanceOf(AdmissibleSet.Completeness.Complete.class,
                completenessOf(LENGTH_BESIDE_AN_ORDER, "email"),
                "the set holds the format and the order, and the bounds the length");
    }

    @Test
    void norWhereTheLengthIsTiedToAnotherPosition() {
        assertInstanceOf(AdmissibleSet.Completeness.Wider.class,
                completenessOf(LENGTH_BOUNDED_BY_A_SIBLING, "pair.left"),
                "what the other position holds changes which lengths are left here");
    }
}
