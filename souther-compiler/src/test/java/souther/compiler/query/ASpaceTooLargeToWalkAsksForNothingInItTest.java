package souther.compiler.query;

import souther.compiler.partition.AdequacyPolicy;
import souther.compiler.partition.Budgets;
import souther.compiler.regex.PatternPlan;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pair space the measure would not walk asks for nothing in it.
 *
 * <p>What a budget on the measure buys is that a space growing with the positions and their classes
 * together is not walked to the end of. Spent there and then made back downstream, it buys nothing:
 * the reader that names what is left walks the same space, one combination at a time, and hands
 * every one of them to the generation as a row to compose.
 *
 * <p>And it would be saying the wrong thing while it did it. What happened is that nobody found out
 * which combinations the rows are in — not that the rows are in none of them. The first is a
 * measurement that did not finish; the second is a model with a gap at every combination it has.
 */
class ASpaceTooLargeToWalkAsksForNothingInItTest {

    /** Four combinations across two positions, which a budget of three does not reach the end of. */
    private static final String MODEL = """
            module example.wide

            data A
            data B
            data Flag = A | B
            data Res = { n: Int }

            behavior pick : (x: Flag, y: Flag) -> Res

            example pick
                | "one" : (A, A) -> Res { n = 1 }
            """;

    /** Nothing is raised at a combination of a space nobody walked. */
    @Test
    void noCombinationOfASpaceNobodyWalkedIsRaised() {
        assertEquals(List.of(), gapsUnder(3),
                "a combination nothing was read about is not a combination no row is in");
        assertTrue(gapsUnder(Budgets.measures().pairSpace()).size() > 1,
                "and the same model walked does raise them, so this is the budget's doing");
    }

    /** And nothing is asked of the search, which is where the space would be made back. */
    @Test
    void nothingIsAskedOfTheSearchEither() {
        Map<String, Adequacy.Filling> filled =
                Adequacy.generatedOf(compiled(3).db(), "example.wide");
        Adequacy.Filling pick = filled == null ? null : filled.get("pick");
        assertTrue(pick == null || pick.composed().plan().pairsOwed().isEmpty(),
                () -> "a row is not owed at a combination nobody established anything about: "
                        + (pick == null ? "nothing was asked" : pick.composed().plan().pairsOwed()));
    }

    private static List<Adequacy.Finding> gapsUnder(int pairSpace) {
        List<Adequacy.Finding> findings =
                compiled(pairSpace).db().ask(new Adequacy.Findings("example.wide")).value();
        return findings == null ? List.of() : findings.stream()
                .filter(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED)
                .toList();
    }

    private static Compilation compiled(int pairSpace) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main")
                .withAdequacyPolicy(new AdequacyPolicy(
                        new AdequacyPolicy.OfTheMeasures(pairSpace,
                                Budgets.measures().cellsPerGroup(),
                                PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                        Budgets.generation()));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
