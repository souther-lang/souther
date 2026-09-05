package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An equality between two positions, read by the reading that says what a position admits.
 *
 * <p>The reading that relates positions to each other is the affine one, and its subjects are the
 * numbers a model adds. Everything else about a position was a product indexed by the position, so
 * {@code p == r} over a carrier the numbers do not hold reached nothing: what the rules stated
 * about {@code p} and what they stated about {@code r} stayed two facts about two places, and a
 * declaration no value of which can be written was admitted.
 *
 * <p>What is asserted here is that it is read, and read the same way whatever the positions are of.
 * A sum and a string are the carriers the numbers do not hold; an {@code Int} is beside them
 * because the two readings answering one clause is not two meanings of it, and the answer has to
 * be the same.
 *
 * <p>Each refusal is written beside the nearest model that does have a value. A reading that held
 * the positions as one and narrowed nothing would refuse both, and what is asserted would be that
 * something was refused rather than that the equality was read.
 */
class AnEqualityBetweenTwoPositionsIsHeldByTheValuesTest {

    private static final String STAGE = """
            module demo

            data Ready
            data Done
            data Stage = Ready | Done

            """;

    private static List<String> saidOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(Located::diagnostic)
                .map(each -> each.said().getClass().getSimpleName())
                .toList();
    }

    private static void refuses(String said, String source) {
        assertEquals(List.of(said), saidOf(source), "no value of this can be written");
    }

    private static void admits(String source) {
        assertEquals(List.of(), saidOf(source), "a value of this can be written");
    }

    /**
     * A sum is a carrier the numbers do not hold, which is the whole of why this went unread.
     *
     * <p>{@code r} is {@code Ready}, {@code p} is what {@code r} is, and {@code p} is not
     * {@code Ready}. Each clause about one position is read; what was not read is the one relating
     * them.
     */
    @Test
    void twoPositionsOfASumHeldAsOneAreOnePosition() {
        refuses("NoValueTheseCanAllHold", STAGE + """
                data Pair = { p: Stage, r: Stage }
                    invariant no = p == r && p /= Ready && r == Ready
                """);
    }

    /** And the same rules without the contradiction leave a value, so what refuses is the pair of
     *  facts and not the equality. */
    @Test
    void andTheSameEqualityOverRulesThatAgreeIsAdmitted() {
        admits(STAGE + """
                data Pair = { p: Stage, r: Stage }
                    invariant ok = p == r && p /= Ready && r == Done
                """);
    }

    /** An equality nothing else narrows says the two are one value and refuses nothing. */
    @Test
    void anEqualityOnItsOwnRefusesNothing() {
        admits(STAGE + """
                data Pair = { p: Stage, r: Stage }
                    invariant same = p == r
                """);
    }

    /** A string is the other carrier the numbers do not hold, and is read the same way. */
    @Test
    void twoStringPositionsHeldAsOneAreOnePosition() {
        refuses("NoValueTheseCanAllHold", """
                module demo

                data Pair = { p: String, r: String }
                    invariant no = p == r && p /= "A" && r == "A"
                """);
    }

    /**
     * And where the two facts are a set and a range rather than two sets, which is the other half
     * of what a position admits.
     *
     * <p>The range the one value is in is every one of their ranges at once. Asked of one member,
     * the pair would be answered against half of what the rules say and would come back holding
     * something.
     */
    @Test
    void whereTheirRangesShareNothingTheyAreRefusedToo() {
        refuses("NoValueItsRulesAllowIsInThatRange", """
                module demo

                data Pair = { p: String, r: String }
                    invariant no = p == r && p < "b" && r > "y"
                """);
    }

    /** And ranges that do share something leave a value. */
    @Test
    void andRangesThatShareSomethingAreAdmitted() {
        admits("""
                module demo

                data Pair = { p: String, r: String }
                    invariant ok = p == r && p < "y" && r > "b"
                """);
    }

    /**
     * Three positions written as two equalities are one value.
     *
     * <p>The closure and not the pair of pairs: nothing says {@code p} and {@code r} are one, and a
     * reading that held only what was written would find no rule they both answer to.
     */
    @Test
    void anEqualityChainHoldsAllThreeAsOne() {
        refuses("NoValueTheseCanAllHold", STAGE + """
                data Trio = { p: Stage, q: Stage, r: Stage }
                    invariant no = p == q && q == r && p == Ready && r == Done
                """);
    }

    /** And the same chain over rules that agree leaves a value. */
    @Test
    void andAChainOverRulesThatAgreeIsAdmitted() {
        admits(STAGE + """
                data Trio = { p: Stage, q: Stage, r: Stage }
                    invariant ok = p == q && q == r && p == Ready && r == Ready
                """);
    }

    /**
     * A branch may not lend its equality to the branch beside it.
     *
     * <p>Neither alternative is one nobody can be in, and what the choice holds as one value is
     * what both of them do — which is neither pair. Held the other way round, this would be refused
     * on the strength of rules that are never all in force at once.
     */
    @Test
    void aChoiceHoldsAsOneOnlyWhatBothBranchesDo() {
        admits(STAGE + """
                data Trio = { p: Stage, r: Stage, s: Stage }
                    invariant either = (p == r) || (p == s)
                """);
    }

    /**
     * An {@code Int} is beside them and not a case of its own.
     *
     * <p>The numbers read this clause as well, and both readings are right. What is asserted is
     * that the answer is the same: a carrier the numbers happen to hold is not a model that gets a
     * different reading.
     */
    @Test
    void andANumberIsRefusedAlike() {
        refuses("NoValueTheseCanAllHold", """
                module demo

                data Pair = { p: Int, r: Int }
                    invariant no = p == r && p /= 1 && r == 1
                """);
    }

    /**
     * A denial between two positions is not this and is not read.
     *
     * <p>An equality says the two are one side of the product. A denial takes the diagonal out of
     * a product, which is not a product — so it reaches no reading here, and this model is one
     * nothing refuses.
     */
    @Test
    void aDenialBetweenTwoPositionsIsNotHeld() {
        admits(STAGE + """
                data Pair = { p: Stage, r: Stage }
                    invariant no = p /= r && p == Ready && r == Ready
                """);
    }
}
