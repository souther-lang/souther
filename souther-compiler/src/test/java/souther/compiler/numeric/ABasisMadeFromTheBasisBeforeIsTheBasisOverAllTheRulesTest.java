package souther.compiler.numeric;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.rule;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;
import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;
import souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.Outcome;

/**
 * Rules of a growing prefix of positions, said one at a time, leave at every step what the same
 * rules leave closed in one run — including the steps that tighten a bound already said, say
 * something that contradicts what was said, or are one of two rules said after the same rules.
 *
 * <p>A basis is made from the basis of the rules before where the rules added are of a kind it is
 * made from, and the steps made that way are counted so that a sequence that was always made over
 * again is not read as one that held.
 */
class ABasisMadeFromTheBasisBeforeIsTheBasisOverAllTheRulesTest {

    private static final List<String> ATOMS = List.of("a", "b", "cc", "d", "e");
    private static final List<String> RELATIONS = List.of("<=", "<", ">=", ">");
    private static final int SEQUENCES = 400;

    private static String prefix(int length) {
        return String.join(" + ", ATOMS.subList(0, length));
    }

    private static Written bound(Random dice, String left) {
        return rule(left + " " + RELATIONS.get(dice.nextInt(4)) + " " + (dice.nextInt(15) - 7));
    }

    /** The rules of a chain over {@code atoms} positions, in the order they are said. */
    private static List<Written> chain(Random dice, int atoms) {
        List<Written> said = new ArrayList<>();
        for (int length = 1; length <= atoms; length++) {
            if (dice.nextInt(3) != 0) {
                said.add(bound(dice, ATOMS.get(length - 1)));
            }
            if (length >= 2) {
                said.add(bound(dice, prefix(length)));
                if (dice.nextInt(3) == 0) {
                    said.add(bound(dice, prefix(length)));
                }
                if (dice.nextInt(3) == 0) {
                    said.add(bound(dice, prefix(1 + dice.nextInt(length))));
                }
            }
        }
        return said;
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.statedOnly(written,
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    private static Outcome alone(List<AffineConstraint<String>> rules, CanonicalOrder<String> order) {
        return RulesNamingNoPositionInCommonCloseApartTest.outcome(ClosedState.closedTogether(rules,
                RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
    }

    private static ClosedStates.Parted<String> asked(ClosedStates kept,
                                                      List<AffineConstraint<String>> rules,
                                                      CanonicalOrder<String> order,
                                                      ClosedStates.Parted<String> before) {
        return kept.of(rules, RulesNamingNoPositionInCommonCloseApartTest::spacing, order, before);
    }

    private static Outcome outcome(ClosedStates.Parted<String> parted) {
        return RulesNamingNoPositionInCommonCloseApartTest.outcome(parted.state());
    }

    /** What the closure answers of the sums of the prefixes, which is what a basis is asked. */
    private static List<PrefixBasis.Highest> sums(ClosedStates.Parted<String> parted) {
        List<PrefixBasis.Highest> out = new ArrayList<>();
        if (parted.state().holdsNothing()) {
            return out;
        }
        for (int length = 1; length <= ATOMS.size(); length++) {
            Map<String, ExactRatio> sum = new java.util.LinkedHashMap<>();
            ATOMS.subList(0, length).forEach(atom -> sum.put(atom, ExactRatio.ONE));
            out.add(parted.state().highestInBasis(sum, ExactRatio.ZERO));
        }
        return out;
    }

    @Test
    void everyStepSaidOneAtATimeIsTheClosureInOneRun() {
        long[] followed = new long[1];
        PrefixBasis.COUNTING_FOLLOWED = followed;
        try {
            Random dice = new Random(316702);
            for (int sequence = 0; sequence < SEQUENCES; sequence++) {
                CanonicalOrder<String> order = RulesNamingNoPositionInCommonCloseApartTest.ORDERS
                        .get(sequence % 2);
                List<AffineConstraint<String>> said = read(chain(dice, 2 + dice.nextInt(4)));
                ClosedStates kept = ClosedStates.keptWithWorkOf(ClosureWork.PLACES_KEPT);
                ClosedStates.Parted<String> before = null;
                for (int at = 1; at <= said.size(); at++) {
                    List<AffineConstraint<String>> sofar = said.subList(0, at);
                    before = asked(kept, sofar, order, before);
                    assertEquals(alone(sofar, order), outcome(before), "said one at a time: " + sofar);
                    ClosedStates.Parted<String> inOneRun =
                            asked(ClosedStates.keptWithWorkOf(ClosureWork.PLACES_KEPT), sofar, order,
                                    null);
                    assertEquals(sums(inOneRun), sums(before), "sums of " + sofar);
                }
            }
        } finally {
            PrefixBasis.COUNTING_FOLLOWED = null;
        }
        assertTrue(followed[0] > 300, "too few bases were made from the one before: " + followed[0]);
    }

    /** Two sets of rules said after the same rules leave each what it leaves alone, and the rules
     *  they were said after leave what they did. */
    @Test
    void twoRulesSaidAfterTheSameRulesDoNotChangeEachOthersClosureOrTheOneBeforeThem() {
        Random dice = new Random(316703);
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            CanonicalOrder<String> order = RulesNamingNoPositionInCommonCloseApartTest.ORDERS
                    .get(sequence % 2);
            List<AffineConstraint<String>> said = read(chain(dice, 3 + dice.nextInt(3)));
            if (said.size() < 3) {
                continue;
            }
            int cut = 2 + dice.nextInt(said.size() - 2);
            List<AffineConstraint<String>> parent = said.subList(0, cut);
            ClosedStates kept = ClosedStates.keptWithWorkOf(ClosureWork.PLACES_KEPT);
            ClosedStates.Parted<String> asParent = asked(kept, parent, order, null);
            Outcome parentOutcome = outcome(asParent);
            List<PrefixBasisBranch> branches = new ArrayList<>();
            for (int branch = 0; branch < 2; branch++) {
                List<AffineConstraint<String>> more = new ArrayList<>(parent);
                more.addAll(read(chain(dice, 5).subList(0, 2)));
                branches.add(new PrefixBasisBranch(more, asked(kept, more, order, asParent)));
            }
            for (PrefixBasisBranch each : branches) {
                assertEquals(alone(each.rules(), order), outcome(each.state()),
                        "a branch of " + parent + ": " + each.rules());
            }
            assertEquals(parentOutcome, outcome(asParent), "the rules before were changed by " + branches);
            assertEquals(parentOutcome, alone(parent, order));
        }
    }

    private record PrefixBasisBranch(List<AffineConstraint<String>> rules,
                                     ClosedStates.Parted<String> state) {}
}
