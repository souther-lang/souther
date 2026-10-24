package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value is one its rules are worked out of and come to true, and what the bounds read of a rule
 * is the rule over the whole numbers.
 *
 * <p>The two come apart wherever an operator stops a run on some operands. Under
 * {@code value + M > 0} the bounds read a value above {@code -M}, and a sum stops at every value
 * above nought. What this holds is that the rules' bounds are not then called the whole of what
 * they leave, that no value is shown where every value stops, and that the operators are found
 * wherever a run works them out — through a binding, a denial, and the side of a choice a run
 * reaches.
 */
class AnInvariantIsReadAsWorkedOutBeforeItIsReadAsTrueTest {

    private static final String MAX = "9223372036854775807";

    private static FieldDomains domainsOf(String rule) {
        return domainsOf("Int", rule);
    }

    private static FieldDomains domainsOf(String carrier, String rule) {
        return domainsOfRules(carrier, "invariant only = " + rule);
    }

    /** {@code invariants} are written whole, one rule to a line. */
    private static FieldDomains domainsOfRules(String carrier, String... invariants) {
        String source = """
                module example.worked

                data Subject = %s
                    %s

                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """.formatted(carrier, String.join("\n    ", invariants));
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        TypeSymbol subject = TypeSymbols.declared(new TypeKey(module, "Subject"));
        return Rules.of(subject, RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY)).bounds();
    }

    private static void holdsNothing(String rule) {
        FieldDomains read = domainsOf(rule);
        assertTrue(read.holdsNothing().isPresent(), rule + " is worked out by no value");
    }

    /** Where some value gets through, the bounds are not the whole of what the rule leaves. */
    @Test
    void aSumThatStopsSomeValuesLeavesTheBoundsShortOfTheRule() {
        FieldDomains read = domainsOf("value + " + MAX + " > 0");
        assertTrue(read.holdsNothing().isEmpty(), "nought gets through the sum");
        assertInstanceOf(ProjectionEvidence.NotCertified.class, read.projection(),
                "the sum stops every value above nought, which the bounds do not say");
    }

    /** And where no value stops, nothing is asked of the bounds. */
    @Test
    void aSumThatStopsNoValueLeavesTheBoundsTheWholeOfTheRule() {
        FieldDomains read = domainsOf("value >= 0 && value <= 100 && value + 1 > 0");
        assertTrue(read.holdsNothing().isEmpty());
        assertInstanceOf(ProjectionEvidence.CertifiedExact.class, read.projection());
    }

    /** The left of a choice is worked out first, so the right is reached where it fails. */
    @Test
    void theSideOfAChoiceAnOtherSideFailsToHoldIsWorkedOut() {
        holdsNothing("value >= 1 && (value == 0 || value + " + MAX + " > 0)");
    }

    /** Where the left may hold, the right is reached only past it, and is not asked of every value. */
    @Test
    void theSideOfAChoiceOnlyReachedPastTheOtherIsNotAskedOfEveryValue() {
        FieldDomains read = domainsOf("value >= 0 && (value == 0 || value + " + MAX + " > 0)");
        assertTrue(read.holdsNothing().isEmpty(), "nought holds the left");
    }

    /** And the bounds are then not called the whole of what the rule leaves. */
    @Test
    void aChoiceWhoseSideMayStopARunLeavesTheBoundsShortOfTheRule() {
        FieldDomains read = domainsOf("value >= 0 && (value == 0 || value + " + MAX + " > 0)");
        assertInstanceOf(ProjectionEvidence.NotCertified.class, read.projection());
    }

    /** A denial carries the operators in it all the same. */
    @Test
    void aSumUnderADenialIsWorkedOut() {
        holdsNothing("value >= 1 && Bool.not(value + " + MAX + " <= 0)");
    }

    /** What is known of the value is all of the rules', whichever clause it was written in. */
    @Test
    void theLeftOfAChoiceIsRefutedByAnotherClauseWhicheverCameFirst() {
        for (boolean choiceFirst : new boolean[] {false, true}) {
            String choice = "invariant choice = value == 0 || value + " + MAX + " > 0";
            String floor = "invariant floor = value >= 1";
            FieldDomains read = choiceFirst ? domainsOfRules("Int", choice, floor)
                    : domainsOfRules("Int", floor, choice);
            assertTrue(read.holdsNothing().isPresent(), "the choice written "
                    + (choiceFirst ? "first" : "second"));
        }
    }

    /** A product of two values is worked out wherever the ends each is held to keep it inside. */
    @Test
    void aProductOfTwoHeldValuesIsReadAsAnswering() {
        FieldDomains read = domainsOf("value >= 1 && value <= 1000 && value * value >= 4");
        assertFalse(read.projection().causes().stream().anyMatch(cause ->
                cause instanceof ProjectionEvidence.Cause.OperatorsStopARunWhereNothingSays));
    }

    /** And where nothing holds them, it may stop a run where no region says. */
    @Test
    void aProductOfTwoUnheldValuesIsNotReadAsAnswering() {
        FieldDomains read = domainsOf("value * value >= 4");
        assertTrue(read.projection().causes().stream().anyMatch(cause ->
                cause instanceof ProjectionEvidence.Cause.OperatorsStopARunWhereNothingSays));
    }

    /** An operand is a value of the type the operator takes, so it is held to what the type holds. */
    @Test
    void aDifferenceOfTwoValuesOfATypeFitsThatType() {
        FieldDomains read = domainsOfRules("{ ys: List<Int>, zs: List<Int> }",
                "invariant apart = List.length(zs) >= 1 && List.length(ys) - List.length(zs) >= "
                        + "9223372036854775806");
        assertTrue(read.holdsNothing().isEmpty(), "a list of the greatest length beside one of one");
        assertInstanceOf(ProjectionEvidence.CertifiedExact.class, read.projection());
    }

    /** An operator no region is written for is not read as answering everywhere. */
    @Test
    void anOperatorWithNoRegionLeavesTheBoundsShortOfTheRule() {
        FieldDomains read = domainsOf("Decimal", "value + 1.5m > 0.0m");
        assertInstanceOf(ProjectionEvidence.NotCertified.class, read.projection(),
                "a Decimal sum may stop a run for want of room, which nothing here says where");
        assertFalse(read.shownToHoldAValue(), "and a value is not shown to get through it");
    }
}
