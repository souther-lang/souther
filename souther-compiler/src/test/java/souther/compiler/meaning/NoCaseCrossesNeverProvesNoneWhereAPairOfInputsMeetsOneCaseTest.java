package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.HOLIDAYS;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.MEMBER;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.X;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.Y;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.relation;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.remainder;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.someCaseCrosses;

/**
 * Where a line at a remainder is proved to decide in none of the cases it is said for, no two
 * inputs of a small domain, one holding the line and one failing it, meet the same case: over cases
 * made by chance, in a seed that is fixed, of numbers, remainders of numbers and an element of a
 * set met by {@code some}, against every pair of inputs.
 *
 * <p>The proof is what leaves cases out of where a line decides, so what it must never do is say
 * "none" where a pair is found, and the rules it is made of are each asked their own claim in
 * {@link NoCaseCrossesProvesNoneWhereAPairOfRowsMeetsOneCaseTest}. This is what asks of the cases
 * put together in ways no one of those thought of; it is a sweep of a domain and so it is deferred
 * to the nightly.
 */
@Nightly
class NoCaseCrossesNeverProvesNoneWhereAPairOfInputsMeetsOneCaseTest {

    /** The numbers an input holds are these, and a set holds some of one to three. */
    private static final int LOW = -2;
    private static final int HIGH = 4;

    /** Every remainder here is of {@code x} by 3 unless a round says otherwise, so that what a
     *  case says of one is read against the line. */
    private static Proposition atom(Random chance) {
        return switch (chance.nextInt(6)) {
            case 0 -> relation(Map.of(X, 1), -chance.nextInt(HIGH), Rel.GE, chance.nextBoolean());
            case 1 -> relation(Map.of(X, 1, Y, -1), chance.nextInt(5) - 2, Rel.GE,
                    chance.nextBoolean());
            case 2, 3 -> relation(Map.of(remainder(X, chance.nextInt(5) - 1, 3), 1),
                    -chance.nextInt(3), chance.nextBoolean() ? Rel.GE : Rel.EQ,
                    chance.nextBoolean());
            case 4 -> relation(Map.of(remainder(Y, chance.nextInt(3), 3), 1), -chance.nextInt(2),
                    Rel.EQ, chance.nextBoolean());
            default -> new Proposition.Some(HOLIDAYS, relation(Map.of(MEMBER, 1, X, -1),
                    chance.nextInt(3) - 1, Rel.EQ, true), chance.nextBoolean());
        };
    }

    private static DecidingCase.Cases cases(Random chance, int depth,
                                            List<DecidingCase.Cases> shareable) {
        if (!shareable.isEmpty() && chance.nextInt(5) == 0) {
            return shareable.get(chance.nextInt(shareable.size()));
        }
        DecidingCase.Cases made;
        if (depth == 0 || chance.nextInt(3) == 0) {
            Proposition condition = chance.nextInt(6) == 0
                    ? Proposition.all(List.of(atom(chance), atom(chance)))
                    : chance.nextInt(8) == 0
                    ? Proposition.any(List.of(atom(chance), atom(chance)))
                    : atom(chance);
            made = new DecidingCase.Cases.One(condition);
        } else if (chance.nextBoolean()) {
            List<DecidingCase.Cases> alternatives = new ArrayList<>();
            for (int i = 0; i < 2 + chance.nextInt(2); i++) {
                alternatives.add(cases(chance, depth - 1, shareable));
            }
            made = new DecidingCase.Cases.EachOf(alternatives);
        } else {
            List<DecidingCase.Cases> factors = new ArrayList<>();
            for (int i = 0; i < 2 + chance.nextInt(2); i++) {
                factors.add(cases(chance, depth - 1, shareable));
            }
            made = DecidingCase.Cases.together(factors);
        }
        shareable.add(made);
        return made;
    }

    private static boolean proves(Proposition.Compared line, DecidingCase.Cases cases) {
        return NoCaseCrosses.proves(line, new DecidingCase(line, cases), _ -> true);
    }

    @Test
    void aProofNeverLeavesOutAPairOfInputsMeetingOneCase() {
        List<TheInputsACaseHoldsFor.Input> inputs = TheInputsACaseHoldsFor.inputs(LOW, HIGH, true);
        Random chance = new Random(20240611);
        int proved = 0;
        int tried = 0;
        for (int round = 0; round < 300; round++) {
            DecidingCase.Cases cases = cases(chance, 3, new ArrayList<>());
            Proposition.Compared line = relation(Map.of(remainder(X, chance.nextInt(3), 3), 1),
                    -chance.nextInt(3), Rel.GE, true);
            tried++;
            if (proves(line, cases)) {
                proved++;
                assertFalse(someCaseCrosses(line, cases, inputs),
                        "proved that no case crosses " + line + ", and two inputs meet one case: "
                                + cases);
            }
        }
        assertTrue(proved > 0 && proved < tried,
                "a proof is made for some of the cases and not for all: " + proved + " of " + tried);
    }
}
