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
    private static final int MANY_QUESTIONS = 40;

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

    @Test
    void theSearchTriesTheSameTruthsAndStopsWhereItDidWhenTheStatementIsWalkedItself() {
        Random random = new Random(3035);
        int capped = 0;
        int refuted = 0;
        int notRefuted = 0;
        for (int drawn = 0; drawn < 120; drawn++) {
            Map<Proposition, Integer> asked = new IdentityHashMap<>();
            List<Proposition> shared = new ArrayList<>();
            Proposition stated = drawn % 3 == 0 ? clauses(random, asked)
                    : statement(random, 7, MANY_QUESTIONS, asked, shared);
            Boolean[] truths = new Boolean[MANY_QUESTIONS];
            for (int at = 0; at < MANY_QUESTIONS; at++) {
                int pick = random.nextInt(8);
                truths[at] = pick == 0 ? Boolean.TRUE : pick == 1 ? Boolean.FALSE : null;
            }
            Boolean[] before = truths.clone();
            WalkedItself walked = new WalkedItself(asked, truths.clone());

            boolean expected = walked.refuted(stated);
            boolean answer = TheCaseALineDecidesIn.noTruthMakesItHold(stated, asked, truths);

            int draw = drawn;
            assertEquals(expected, answer, () -> "the " + draw + "th draw");
            assertArrayEquals(before, truths, "the truths are as they were");
            if (walked.tried > TheCaseALineDecidesIn.TRUTHS_TRIED) {
                capped++;
            }
            if (answer) {
                refuted++;
            } else {
                notRefuted++;
            }
        }
        int some = capped;
        int yes = refuted;
        int no = notRefuted;
        assertTrue(some >= 2 && yes > 10 && no > 10,
                () -> some + " past the truths tried, " + refuted(yes, no));
    }

    /** Every one of some alternatives of three questions held, drawn at random: a statement that
     *  most often holds under no truth, which a search refutes only by trying a great many. */
    private static Proposition clauses(Random random, Map<Proposition, Integer> asked) {
        List<Proposition> all = new ArrayList<>();
        for (int each = 0; each < 43 * MANY_QUESTIONS / 10; each++) {
            List<Proposition> literals = new ArrayList<>();
            for (int at = 0; at < 3; at++) {
                int question = random.nextInt(MANY_QUESTIONS);
                boolean holds = random.nextBoolean();
                Proposition literal = new Proposition.Truth(
                        new DecisionSubject.AnInput(TermPath.of("q" + question)), holds);
                asked.put(literal, holds ? question + 1 : -(question + 1));
                literals.add(literal);
            }
            Proposition clause = new Proposition.Any(literals);
            asked.put(clause, 0);
            all.add(clause);
        }
        Proposition stated = new Proposition.All(all);
        asked.put(stated, 0);
        return stated;
    }

    /** The search as it was when it walked the statement itself, a table of what each part came
     *  to emptied before each walk: what the numbered nodes are held to. */
    private static final class WalkedItself {

        private static final Object OPEN = new Object();

        private final Map<Proposition, Integer> asked;
        private final Boolean[] truths;
        private final Map<Proposition, Object> worked = new IdentityHashMap<>();
        private int tried;
        private int firstOpen;

        WalkedItself(Map<Proposition, Integer> asked, Boolean[] truths) {
            this.asked = asked;
            this.truths = truths;
        }

        boolean refuted(Proposition stated) {
            firstOpen = 0;
            worked.clear();
            Boolean now = valueOf(stated);
            if (now != null) {
                return !now;
            }
            if (++tried > TheCaseALineDecidesIn.TRUTHS_TRIED || firstOpen == 0) {
                return false;
            }
            int at = Math.abs(firstOpen) - 1;
            Boolean held = firstOpen > 0;
            for (Boolean truth : List.of(held, !held)) {
                truths[at] = truth;
                boolean refuted = refuted(stated);
                truths[at] = null;
                if (!refuted) {
                    return false;
                }
            }
            return true;
        }

        private Boolean valueOf(Proposition stated) {
            Object had = worked.get(stated);
            if (had != null) {
                return had == OPEN ? null : (Boolean) had;
            }
            Boolean out = valueOnce(stated);
            worked.put(stated, out == null ? OPEN : out);
            return out;
        }

        private Boolean valueOnce(Proposition stated) {
            return switch (stated) {
                case Proposition.All all -> {
                    boolean open = false;
                    for (Proposition part : all.parts()) {
                        Boolean one = valueOf(part);
                        if (Boolean.FALSE.equals(one)) {
                            yield false;
                        }
                        open |= one == null;
                    }
                    yield open ? null : true;
                }
                case Proposition.Any any -> {
                    boolean open = false;
                    for (Proposition part : any.parts()) {
                        Boolean one = valueOf(part);
                        if (Boolean.TRUE.equals(one)) {
                            yield true;
                        }
                        open |= one == null;
                    }
                    yield open ? null : false;
                }
                default -> {
                    int signed = asked.get(stated);
                    if (signed == 0) {
                        yield null;
                    }
                    Boolean truth = truths[Math.abs(signed) - 1];
                    if (truth == null && firstOpen == 0) {
                        firstOpen = signed;
                    }
                    yield truth == null ? null : truth == signed > 0;
                }
            };
        }
    }

    private static String refuted(int some, int others) {
        return "refuted " + some + ", not refuted " + others;
    }

    private static Proposition statement(Random random, int depth, Map<Proposition, Integer> asked,
                                         List<Proposition> shared) {
        return statement(random, depth, QUESTIONS, asked, shared);
    }

    private static Proposition statement(Random random, int depth, int questions,
                                         Map<Proposition, Integer> asked,
                                         List<Proposition> shared) {
        if (!shared.isEmpty() && random.nextInt(5) == 0) {
            return shared.get(random.nextInt(shared.size()));
        }
        int kind = random.nextInt(depth == 0 ? 3 : 5);
        Proposition made = switch (kind) {
            case 0, 1 -> {
                int question = random.nextInt(questions);
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
                    parts.add(statement(random, depth - 1, questions, asked, shared));
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
