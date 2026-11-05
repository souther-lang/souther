package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A case is refuted under some truths settled ({@link TheCaseALineDecidesIn#noTruthMakesItHold})
 * exactly where every truth of the questions left open makes it fail, a part that is no question
 * failing it whichever way it comes out.
 *
 * <p>The oracle tries every truth of the open questions and works the statement out with a part
 * that is no question read as neither, failing a conjunction only where another part fails it and
 * holding an alternative only where another part holds it. Statements are drawn at random from a
 * fixed seed over six questions, a part asked and its denial at one place negated, some parts no
 * question, and parts shared between the conjunctions and alternatives that hold them, to a
 * depth of four.
 */
class ACaseIsRefutedOnlyWhereNoTruthOfItsOpenPartsMakesItHoldTest {

    private static final int QUESTIONS = 6;

    @Test
    void refutedExactlyWhereEveryTruthOfTheOpenQuestionsMakesItFail() {
        Random random = new Random(3032);
        int refuted = 0;
        int notRefuted = 0;
        for (int drawn = 0; drawn < 2000; drawn++) {
            Map<Proposition, Integer> asked = new IdentityHashMap<>();
            List<Proposition> shared = new ArrayList<>();
            Proposition stated = statement(random, 4, asked, shared);
            Boolean[] truths = new Boolean[QUESTIONS];
            for (int at = 0; at < QUESTIONS; at++) {
                int pick = random.nextInt(3);
                truths[at] = pick == 0 ? Boolean.TRUE : pick == 1 ? Boolean.FALSE : null;
            }
            Boolean[] before = truths.clone();

            boolean answer = TheCaseALineDecidesIn.noTruthMakesItHold(stated, asked, truths);

            assertEquals(everyTruthFails(stated, asked, truths), answer, stated::toString);
            assertArrayEquals(before, truths, "the truths are as they were");
            if (answer) {
                refuted++;
            } else {
                notRefuted++;
            }
        }
        int some = refuted;
        int others = notRefuted;
        assertTrue(some > 100 && others > 100, () -> refuted(some, others));
    }

    private static String refuted(int some, int others) {
        return "refuted " + some + ", not refuted " + others;
    }

    private static Proposition statement(Random random, int depth, Map<Proposition, Integer> asked,
                                         List<Proposition> shared) {
        if (!shared.isEmpty() && random.nextInt(5) == 0) {
            return shared.get(random.nextInt(shared.size()));
        }
        int kind = random.nextInt(depth == 0 ? 3 : 5);
        Proposition made = switch (kind) {
            case 0, 1 -> {
                int question = random.nextInt(QUESTIONS);
                boolean holds = random.nextBoolean();
                Proposition part = new Proposition.Truth(
                        new DecisionSubject.AnInput(TermPath.of("q" + question)), holds);
                asked.put(part, holds ? question + 1 : -(question + 1));
                yield part;
            }
            case 2 -> {
                Proposition part = new Proposition.Truth(
                        new DecisionSubject.AnInput(TermPath.of("r" + random.nextInt(3))), true);
                asked.put(part, 0);
                yield part;
            }
            default -> {
                List<Proposition> parts = new ArrayList<>();
                for (int each = 0; each < 2 + random.nextInt(2); each++) {
                    parts.add(statement(random, depth - 1, asked, shared));
                }
                Proposition joined = kind == 3 ? new Proposition.All(parts)
                        : new Proposition.Any(parts);
                asked.put(joined, 0);
                yield joined;
            }
        };
        shared.add(made);
        return made;
    }

    private static boolean everyTruthFails(Proposition stated, Map<Proposition, Integer> asked,
                                           Boolean[] settled) {
        List<Integer> open = new ArrayList<>();
        for (int at = 0; at < QUESTIONS; at++) {
            if (settled[at] == null) {
                open.add(at);
            }
        }
        for (int chosen = 0; chosen < 1 << open.size(); chosen++) {
            Boolean[] truths = settled.clone();
            for (int at = 0; at < open.size(); at++) {
                truths[open.get(at)] = (chosen & 1 << at) != 0;
            }
            if (!Boolean.FALSE.equals(valueOf(stated, asked, truths))) {
                return false;
            }
        }
        return true;
    }

    private static Boolean valueOf(Proposition stated, Map<Proposition, Integer> asked,
                                   Boolean[] truths) {
        return switch (stated) {
            case Proposition.All all -> {
                Boolean out = true;
                for (Proposition part : all.parts()) {
                    Boolean one = valueOf(part, asked, truths);
                    if (Boolean.FALSE.equals(one)) {
                        yield false;
                    }
                    out = one == null ? null : out;
                }
                yield out;
            }
            case Proposition.Any any -> {
                Boolean out = false;
                for (Proposition part : any.parts()) {
                    Boolean one = valueOf(part, asked, truths);
                    if (Boolean.TRUE.equals(one)) {
                        yield true;
                    }
                    out = one == null ? null : out;
                }
                yield out;
            }
            default -> {
                int signed = asked.get(stated);
                yield signed == 0 ? null : truths[Math.abs(signed) - 1] == signed > 0;
            }
        };
    }
}
