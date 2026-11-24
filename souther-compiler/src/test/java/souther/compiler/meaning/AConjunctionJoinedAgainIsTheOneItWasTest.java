package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A conjunction or disjunction joined again from its own parts is the one it was.
 *
 * <p>Every one is made by joining its parts ({@link Proposition#all}, {@link Proposition#any}):
 * each kept once, in the order of their spellings, nested ones of the same kind laid out, and
 * the same one handed out for an equal one made again. A reader putting something through a
 * statement may then hand back a part it changed nothing in as the part it is, rather than
 * joining it again, and come to the statement joining would have.
 *
 * <p>Drawn at random from a fixed seed: truths of a few positions, said to hold and not to, held
 * together and as alternatives, denied, to a depth of four.
 */
class AConjunctionJoinedAgainIsTheOneItWasTest {

    private static final List<String> AT = List.of("a", "b", "c", "d");

    @Test
    void joiningThePartsOfAJoinedStatementGivesItBack() {
        Random random = new Random(2869);
        for (int drawn = 0; drawn < 2000; drawn++) {
            everyJoinedPartIsItsOwnJoining(statement(random, 4));
        }
    }

    private static void everyJoinedPartIsItsOwnJoining(Proposition stated) {
        switch (stated) {
            case Proposition.All all -> {
                assertSame(stated, Proposition.all(all.parts()), stated::toString);
                all.parts().forEach(AConjunctionJoinedAgainIsTheOneItWasTest
                        ::everyJoinedPartIsItsOwnJoining);
            }
            case Proposition.Any any -> {
                assertSame(stated, Proposition.any(any.parts()), stated::toString);
                any.parts().forEach(AConjunctionJoinedAgainIsTheOneItWasTest
                        ::everyJoinedPartIsItsOwnJoining);
            }
            default -> { }
        }
    }

    private static Proposition statement(Random random, int depth) {
        int kind = random.nextInt(depth == 0 ? 1 : 4);
        if (kind == 0) {
            return new Proposition.Truth(new DecisionSubject.AnInput(
                    TermPath.of(AT.get(random.nextInt(AT.size())))), random.nextBoolean());
        }
        List<Proposition> parts = new ArrayList<>();
        for (int at = 0; at < 2 + random.nextInt(3); at++) {
            parts.add(statement(random, depth - 1));
        }
        Proposition joined = kind == 1 ? Proposition.all(parts) : Proposition.any(parts);
        return kind == 3 ? joined.denied() : joined;
    }
}
