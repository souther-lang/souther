package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.values.AdmissibleSet;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

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

    private static AdmissibleSet.Completeness completenessOf(String source, String parameter) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("f"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none()).positions().stream()
                .filter(p -> p.path().toString().equals(parameter))
                .findFirst().orElseThrow().completeness();
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
