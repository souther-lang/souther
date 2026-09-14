package souther.compiler.values;

import org.junit.jupiter.api.Test;

import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternRead;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * One pattern is one machine however many rules write it.
 *
 * <p>A plan says what would be built and is told from another by that. The same pattern written into
 * three rules is one machine and is paid for once — which is what a position's allowance is spent
 * against, so it is not a nicety: a plan that is two plans is a machine built twice, an allowance
 * spent twice, and a refusal where there was none.
 *
 * <p><b>So nothing about who wrote it may reach the identity.</b> Which rules asked is a fact about
 * the model and is worth keeping; kept here, two rules writing one pattern became two things to
 * build, and the answer a model comes to turned on how many times somebody wrote the same clause.
 */
class OnePatternIsOneMachineHoweverOftenItIsWrittenTest {

    private static AdmittedPlan matching(String regex) {
        PatternRead said = PatternParser.read(regex);
        return new AdmittedPlan.Pattern(PatternPlan.of(
                assertInstanceOf(PatternRead.Read.class, said).syntax()));
    }

    /** Two rules writing one pattern, which is one thing to build. */
    @Test
    void thePatternWrittenTwiceIsOnePlan() {
        assertEquals(matching("a{300}"), matching("a{300}"),
                "a plan is told from another by what would be built, and the same pattern written"
                        + " twice would build the same machine");
    }

    /** And met with itself it is itself, which is what a meet of one part comes to. */
    @Test
    void meetingOnePatternWithItselfIsThatPattern() {
        assertEquals(matching("a{300}"),
                AdmittedPlan.meeting(List.of(matching("a{300}"), matching("a{300}"))),
                "two rules stating one pattern leave the position where one of them does, and the"
                        + " work of finding that out is done once");
    }

    /**
     * And what a reading asked for says which position it asked for it.
     *
     * <p>The other half of one plan being one plan. A machine is the pattern's and an allowance is
     * the position's, so a machine refused while one position was worked out is nothing another
     * position's rules asked for — and the pattern alone cannot say that, since it is the same
     * pattern wherever it is written. Kept as the pattern alone, a rule that wrote it about
     * somewhere else would be answerable for a refusal that happened elsewhere.
     */
    @Test
    void whatAReadingAskedForSaysWhichPositionItAskedFor() {
        AdmittedPlan pattern = matching("a{300}");

        assertEquals(java.util.Set.of(new PlannedValues.Asked<>("here", planOf(pattern))),
                PlannedValues.at("here", pattern).asked(),
                "one machine, asked for the position it is being built for");
        assertEquals(java.util.Set.of(new PlannedValues.Asked<>("elsewhere", planOf(pattern))),
                PlannedValues.at("elsewhere", pattern).asked(),
                "and the same pattern about another position is another asking");
    }

    private static PatternPlan planOf(AdmittedPlan plan) {
        return assertInstanceOf(AdmittedPlan.Pattern.class, plan).plan();
    }
}
