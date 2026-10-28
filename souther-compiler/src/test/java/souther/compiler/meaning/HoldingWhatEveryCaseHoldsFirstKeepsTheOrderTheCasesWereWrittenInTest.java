package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Cases put with what every case holds first are the cases they were, with that put before the
 * choices.
 *
 * <p>Two things are held. Of cases no case of which is held twice, the order is the one a walk
 * down them gives, written out as a tree: a group inside a group gives its parts that every case
 * holds and its choices to the group around it, each in the order they were written, and a choice
 * is put in order on its own. And of cases that share, drawn at random, the cases they stand for
 * are the same set: a group that more than one case holds is kept as a case of its own and not
 * copied into each, which changes where its parts are asked and not which cases there are.
 */
class HoldingWhatEveryCaseHoldsFirstKeepsTheOrderTheCasesWereWrittenInTest {

    private static Proposition truth(int at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("t" + at)), true);
    }

    /** The order written out as a tree: what every case of a group holds, then its choices. */
    private static DecidingCase.Cases asATree(DecidingCase.Cases cases) {
        return switch (cases) {
            case DecidingCase.Cases.One _, DecidingCase.Cases.NotTakenApart _ -> cases;
            case DecidingCase.Cases.EachOf(var alternatives) -> new DecidingCase.Cases.EachOf(
                    alternatives.stream().map(
                            HoldingWhatEveryCaseHoldsFirstKeepsTheOrderTheCasesWereWrittenInTest::asATree)
                            .toList());
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> held = new ArrayList<>();
                List<DecidingCase.Cases> choices = new ArrayList<>();
                gather(factors, held, choices);
                held.addAll(choices);
                yield new DecidingCase.Cases.Together(held);
            }
        };
    }

    private static void gather(List<DecidingCase.Cases> factors, List<DecidingCase.Cases> held,
                               List<DecidingCase.Cases> choices) {
        for (DecidingCase.Cases factor : factors) {
            switch (factor) {
                case DecidingCase.Cases.One _ -> held.add(factor);
                case DecidingCase.Cases.Together(var inner) -> gather(inner, held, choices);
                case DecidingCase.Cases.EachOf _, DecidingCase.Cases.NotTakenApart _ ->
                        choices.add(asATree(factor));
            }
        }
    }

    /**
     * Cases drawn at random, up to {@code depth} deep. A case drawn before is held again with a
     * chance of {@code sharing} in five; none is where it is nought.
     */
    private static DecidingCase.Cases drawn(Random dice, int depth, List<DecidingCase.Cases> before,
                                            int sharing, boolean nobodyTookApart) {
        if (!before.isEmpty() && dice.nextInt(5) < sharing) {
            return before.get(dice.nextInt(before.size()));
        }
        int kind = depth == 0 ? dice.nextInt(2) : dice.nextInt(6);
        DecidingCase.Cases made = switch (kind) {
            case 0 -> new DecidingCase.Cases.One(truth(dice.nextInt(6)));
            case 1 -> nobodyTookApart && dice.nextInt(8) == 0
                    ? new DecidingCase.Cases.NotTakenApart(
                            CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN)
                    : new DecidingCase.Cases.One(truth(dice.nextInt(6)));
            case 2, 3 -> new DecidingCase.Cases.EachOf(
                    group(dice, depth, before, dice.nextInt(3), sharing, nobodyTookApart));
            default -> new DecidingCase.Cases.Together(
                    group(dice, depth, before, dice.nextInt(4), sharing, nobodyTookApart));
        };
        before.add(made);
        return made;
    }

    private static List<DecidingCase.Cases> group(Random dice, int depth,
                                                  List<DecidingCase.Cases> before, int size,
                                                  int sharing, boolean nobodyTookApart) {
        List<DecidingCase.Cases> out = new ArrayList<>();
        for (int at = 0; at < size; at++) {
            out.add(drawn(dice, depth - 1, before, sharing, nobodyTookApart));
        }
        return out;
    }

    @Test
    void casesNoneOfWhichIsHeldTwiceArePutInTheOrderTheTreeOfThemIsPutIn() {
        Random dice = new Random(2680);
        int together = 0;
        for (int round = 0; round < 3000; round++) {
            DecidingCase.Cases cases = drawn(dice, 4, new ArrayList<>(), 0, true);
            assertEquals(asATree(cases), CasesOfALineAsked.heldFirst(cases), "for " + cases);
            if (cases instanceof DecidingCase.Cases.Together) {
                together++;
            }
        }
        assertTrue(together > 100, "groups are drawn, or this asks nothing of them: " + together);
    }

    @Test
    void casesThatShareStandForTheSameCasesOnceTheyArePutInOrder() {
        Random dice = new Random(2681);
        int shared = 0;
        for (int round = 0; round < 3000; round++) {
            DecidingCase.Cases cases = drawn(dice, 4, new ArrayList<>(), 2, false);
            Set<Proposition> expected = new HashSet<>(DecidingCases.eachOf(cases));
            assertEquals(expected, new HashSet<>(DecidingCases.eachOf(
                    CasesOfALineAsked.heldFirst(cases))), "for " + cases);
            if (cases.references().values().stream().anyMatch(held -> held > 1)) {
                shared++;
            }
        }
        assertTrue(shared > 300, "cases that share are drawn, or this asks nothing of them: "
                + shared);
    }

    @Test
    void aGroupInsideAGroupGivesItsHeldPartsAndItsChoicesToTheGroupAroundIt() {
        DecidingCase.Cases a = new DecidingCase.Cases.One(truth(1));
        DecidingCase.Cases b = new DecidingCase.Cases.One(truth(2));
        DecidingCase.Cases choice = new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.One(truth(3)), new DecidingCase.Cases.One(truth(4))));
        DecidingCase.Cases inner = new DecidingCase.Cases.Together(List.of(choice, b));
        DecidingCase.Cases outer = new DecidingCase.Cases.Together(List.of(inner, a));

        assertEquals(new DecidingCase.Cases.Together(List.of(b, a, choice)),
                CasesOfALineAsked.heldFirst(outer));
    }

    @Test
    void aGroupMoreThanOneCaseHoldsStaysACaseOfItsOwnInEach() {
        DecidingCase.Cases a = new DecidingCase.Cases.One(truth(1));
        DecidingCase.Cases b = new DecidingCase.Cases.One(truth(2));
        DecidingCase.Cases shared = new DecidingCase.Cases.Together(List.of(a, b));
        DecidingCase.Cases outer = new DecidingCase.Cases.Together(List.of(shared, shared));

        DecidingCase.Cases ordered = CasesOfALineAsked.heldFirst(outer);

        assertEquals(new DecidingCase.Cases.Together(List.of(shared, shared)), ordered);
        assertEquals(4, ordered.references().size(),
                "the outer group, the one group held twice, and its two parts");
    }
}
