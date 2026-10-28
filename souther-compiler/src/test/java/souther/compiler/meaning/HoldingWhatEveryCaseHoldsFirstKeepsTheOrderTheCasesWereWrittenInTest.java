package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Cases put with what every case holds first are the cases a group written inside a group would
 * have been put as, written out as a tree.
 *
 * <p>The ordering is a fold over cases that share what follows from a choice, so each case is put in
 * order once. Written out as a tree it is the walk it replaced: a group inside a group gives its
 * parts that every case holds and its choices to the group around it, each in the order they were
 * written, and a choice is put in order on its own. Held to that on cases drawn at random, some
 * of them sharing a case between two places.
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

    /** Cases drawn at random, up to {@code depth} deep, reusing a case drawn before now and then. */
    private static DecidingCase.Cases drawn(Random dice, int depth, List<DecidingCase.Cases> before) {
        int kind = depth == 0 ? dice.nextInt(2) : dice.nextInt(6);
        if (!before.isEmpty() && dice.nextInt(5) == 0) {
            return before.get(dice.nextInt(before.size()));
        }
        DecidingCase.Cases made;
        switch (kind) {
            case 0 -> made = new DecidingCase.Cases.One(truth(dice.nextInt(6)));
            case 1 -> made = dice.nextInt(8) == 0
                    ? new DecidingCase.Cases.NotTakenApart(
                            CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN)
                    : new DecidingCase.Cases.One(truth(dice.nextInt(6)));
            case 2, 3 -> made = new DecidingCase.Cases.EachOf(
                    group(dice, depth, before, dice.nextInt(3)));
            default -> made = new DecidingCase.Cases.Together(
                    group(dice, depth, before, dice.nextInt(4)));
        }
        before.add(made);
        return made;
    }

    private static List<DecidingCase.Cases> group(Random dice, int depth,
                                                  List<DecidingCase.Cases> before, int size) {
        List<DecidingCase.Cases> out = new ArrayList<>();
        for (int at = 0; at < size; at++) {
            out.add(drawn(dice, depth - 1, before));
        }
        return out;
    }

    @Test
    void casesDrawnAtRandomArePutInTheOrderTheTreeOfThemIsPutIn() {
        Random dice = new Random(2680);
        int together = 0;
        for (int round = 0; round < 3000; round++) {
            DecidingCase.Cases cases = drawn(dice, 4, new ArrayList<>());
            DecidingCase.Cases expected = asATree(cases);
            assertEquals(expected, CasesOfALineAsked.heldFirst(cases), "for " + cases);
            if (cases instanceof DecidingCase.Cases.Together) {
                together++;
            }
        }
        assertTrue(together > 100, "groups are drawn, or this asks nothing of them: " + together);
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
}
