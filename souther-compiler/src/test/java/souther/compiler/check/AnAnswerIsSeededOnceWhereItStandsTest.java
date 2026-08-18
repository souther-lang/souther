package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A call is seeded where it stands, and not once for every node standing over it.
 *
 * <p>What a behavior's answer guarantees is read ahead of the walk, because a construction is judged
 * at its own step while the answers it is built from stand underneath it. Read from every node of
 * the walk as well, it is read again over the whole of each node's subtree — which decides nothing,
 * since the reading is threaded down and the second lands on the subjects the first wrote, and costs
 * the depth of a body over again at every node of it.
 *
 * <p>Held as a count and not as a duration. What is wrong with reading it again is that the work is
 * quadratic in the depth of a body, and a body twice as deep is the input that says so; a
 * millisecond figure would say it on this machine on this day. Bodies of a nesting the source can
 * write, so what is measured is what an author can hand over.
 *
 * <p>Nothing here reports anything, so this is read off {@link PathEngine#SEEDED} — two readings
 * that differ only in how often they seed answer exactly alike about every program, and a difference
 * nothing can read stops being true without anything failing.
 */
class AnAnswerIsSeededOnceWhereItStandsTest {

    /**
     * A body whose whole of it is one region: {@code depth} calls nested inside one another, with no
     * branch, no block and no binding between them to end the reading early. Each call answers a type
     * with an invariant, so each of them is an answer the seeding reads.
     */
    private static String nested(int depth) {
        StringBuilder call = new StringBuilder("a");
        for (int i = 0; i < depth; i++) {
            call.insert(0, "step(").append(")");
        }
        return """
                module demo exposing ( Amount, step, run )

                data Amount = Int
                    invariant value >= 0

                behavior step : (a: Amount) -> Amount
                    constructs Amount

                let step (a) = Amount(a.value + 1)

                behavior run : (a: Amount) -> Amount
                    constructs Amount

                let run (a) = Amount(%s.value + 1)
                """.formatted(call);
    }

    /** Every answer the check seeded while compiling {@code source}, one entry per seeding. */
    private static List<Core> seededIn(String source) {
        List<Core> seeded = Collections.synchronizedList(new ArrayList<>());
        PathEngine.SEEDED = seeded;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            PathEngine.SEEDED = null;
        }
        return List.copyOf(seeded);
    }

    /**
     * A construction given a helper call in one field and an answer in another. {@code HelperInliner}
     * writes the call out as bindings around the helper's body, so the first field holds a binding
     * standing inside a value — which the walk enters by putting the body where the binding was and
     * reading the whole expression from there. The answer in the second field is standing beside it,
     * and was read where the region was entered.
     */
    private static String beside(int helpers, int answers) {
        StringBuilder left = new StringBuilder("a");
        for (int i = 0; i < helpers; i++) {
            left.insert(0, "bump(").append(")");
        }
        StringBuilder right = new StringBuilder("a");
        for (int i = 0; i < answers; i++) {
            right.insert(0, "step(").append(")");
        }
        return """
                module demo exposing ( Amount, Pair, step, run )

                data Amount = Int
                    invariant value >= 0

                data Pair = { l: Amount, r: Amount }

                behavior step : (a: Amount) -> Amount
                    constructs Amount

                let step (a) = Amount(a.value + 1)

                let bump (x: Amount): Amount = Amount(x.value + 1)

                behavior run : (a: Amount) -> Pair
                    constructs Pair, Amount

                let run (a) = Pair { l = %s, r = %s }
                """.formatted(left, right);
    }

    /** Every answer seeded while compiling {@code source} is a distinct one, and there are
     * {@code expected} of them. */
    private static void seededOnce(int expected, String source, String what) {
        List<Core> seeded = seededIn(source);
        Map<Core, Boolean> distinct = new IdentityHashMap<>();
        seeded.forEach(answer -> distinct.put(answer, true));
        assertEquals(expected, distinct.size(), "answers seeded over " + what);
        assertEquals(distinct.size(), seeded.size(), "an answer was seeded twice over " + what);
    }

    @Test
    void anAnswerBesideAnEnteredBindingIsNotReadAgain() {
        for (int helpers : List.of(1, 2, 3)) {
            for (int answers : List.of(1, 2, 4)) {
                seededOnce(answers, beside(helpers, answers),
                        answers + " answers beside " + helpers + " expanded helper calls");
            }
        }
    }

    /**
     * A conditional in one field, and answers standing beside it in another. A conditional given to
     * a value is one of its two branches, so the walk reads the expression once with each branch put
     * where the conditional stood — two readings of the branch, and one of everything else.
     */
    private static String besideAConditional(int answers) {
        StringBuilder right = new StringBuilder("a");
        for (int i = 0; i < answers; i++) {
            right.insert(0, "step(").append(")");
        }
        return """
                module demo exposing ( Amount, Pair, step, run )

                data Amount = Int
                    invariant value >= 0

                data Pair = { l: Amount, r: Amount }

                behavior step : (a: Amount) -> Amount
                    constructs Amount

                let step (a) = Amount(a.value + 1)

                behavior run : (a: Amount) -> Pair
                    constructs Pair, Amount

                let run (a) = Pair { l = if a.value > 3 then Amount(1) else Amount(2), r = %s }
                """.formatted(right);
    }

    @Test
    void anAnswerBesideAnOpenedConditionalIsNotReadAgain() {
        for (int answers : List.of(1, 2, 4)) {
            seededOnce(answers, besideAConditional(answers),
                    answers + " answers beside a conditional in a value");
        }
    }

    /**
     * Where a conditional is, and where the answer stands relative to it. The walk opens a
     * conditional a value is handed by reading the expression once with each branch put where it
     * stood, so every one of these is a place the same answer could be read twice.
     */
    private static final String SUM = """
            module demo exposing ( Amount, Pair, Tag, step, run )

            data Amount = Int
                invariant value >= 0

            data Pair = { l: Amount, r: Amount }

            data Tag = Lo | Hi

            behavior step : (a: Amount) -> Amount
                constructs Amount

            let step (a) = Amount(a.value + 1)

            behavior run : (a: Amount, t: Tag) -> Pair
                constructs Pair, Amount

            """;

    @Test
    void anAnswerAConditionalIsDecidedByIsNotReadAgain() {
        seededOnce(1, SUM + """
                let run (a, t) = Pair
                    { l = if step(a).value > 3 then Amount(1) else Amount(2)
                    , r = a
                    }
                """, "an answer in the condition of a conditional in a value");
    }

    @Test
    void anAnswerPastWhereTheReadingStoppedIsReadByTheRegionThatOwnsIt() {
        seededOnce(1, SUM + """
                let run (a, t) = Pair
                    { l = match t with
                            | Lo -> if step(a).value > 3 then Amount(1) else Amount(2)
                            | Hi -> Amount(9)
                    , r = a
                    }
                """, "an answer in a condition an arm stands over");
        seededOnce(1, SUM + """
                let run (a, t) = Pair
                    { l = match t with
                            | Lo -> if a.value > 3 then Amount(1) else Amount(step(a).value)
                            | Hi -> Amount(9)
                    , r = a
                    }
                """, "an answer in a branch an arm stands over");
        seededOnce(1, SUM + """
                let run (a, t) = Pair
                    { l = match t with
                            | Lo -> if a.value > 3 then Amount(1) else Amount(2)
                            | Hi -> Amount(9)
                    , r = step(a)
                    }
                """, "an answer beside a conditional an arm stands over");
    }

    @Test
    void aCallNestedInsideAnotherIsSeededOnce() {
        for (int depth : List.of(1, 2, 4, 8, 16)) {
            seededOnce(depth, nested(depth), "a body of " + depth + " nested calls");
        }
    }
}
