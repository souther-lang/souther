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
 * An answer is read once for each reading of its region that it stands in.
 *
 * <p>What a behavior's answer guarantees is read ahead of the walk, because a construction is judged
 * at its own step while the answers it is built from stand underneath it. How far ahead is where the
 * reading stops, and everything it covered is then walked over what it settled — so reading it again
 * from a descendant, or from an expression rebuilt around it, lands on the subjects it already holds.
 * It decides nothing, and it costs the depth of a body over again at every node of it (#826).
 *
 * <p>Nothing else decides the count. Not how deep the answer stands, not how many stand beside it,
 * not whether a binding an expansion introduced or a branch of a conditional was put in above it.
 * What does decide it is how many readings of its region there are, and that is a conditional a value
 * is handed: opening one reads the expression once with each branch standing where it stood, so an
 * answer in a region standing under it is read by both — which is the same two that judge every
 * construction inside it and say what they found once ({@link InvariantChecker.Judgment#of}).
 *
 * <p>Held as a count and not as a duration, and against a growing number of answers rather than at
 * one size: what is wrong with reading them again is that the work grows with what it is read over,
 * and a body with twice the answers is the input that says so. A millisecond figure would say it on
 * this machine on this day.
 *
 * <p>Nothing here reports anything, so this is read off {@link PathEngine#SEEDED} — two readings
 * that differ only in how often they seed answer exactly alike about every program, and a difference
 * nothing can read stops being true without anything failing.
 */
class AnAnswerIsSeededOnceWhereItStandsTest {

    /** {@code answers} nested calls, each of them an answer the seeding reads. */
    private static String answers(int answers) {
        StringBuilder call = new StringBuilder("a");
        for (int i = 0; i < answers; i++) {
            call.insert(0, "step(").append(")");
        }
        return call.toString();
    }

    /**
     * The declarations every body below is written against. {@code bump} is a helper and not a
     * behavior, so a call to it is written out as bindings around its body — which is a binding
     * standing inside a value, and one of the two places the walk rebuilds an expression to enter.
     */
    private static final String DECLARATIONS = """
            module demo exposing ( Amount, Pair, Box, Tag, step, run )

            data Amount = Int
                invariant value >= 0

            data Pair = { l: Amount, r: Amount }

            data Box = { p: Pair, q: Amount }

            data Tag = Lo | Hi

            behavior step : (a: Amount) -> Amount
                constructs Amount

            let step (a) = Amount(a.value + 1)

            let bump (x: Amount): Amount = Amount(x.value + 1)

            behavior run : (a: Amount, t: Tag) -> Box
                constructs Box, Pair, Amount

            """;

    /** Somewhere an answer can stand, and how many readings of the region it stands in there are.
     * {@code $A} is where the answers go. */
    private record Place(String what, int readings, String body) {}

    private static Place read(String what, String body) {
        return new Place(what, 1, body);
    }

    private static Place readTwice(String what, String body) {
        return new Place(what, 2, body);
    }

    /**
     * Every place an answer can stand relative to what makes the walk rebuild an expression.
     *
     * <p>A binding an expansion introduced and a conditional a value is handed are the two, and an
     * answer can stand on its own, beside one, in what decides one, in what one puts in, or in a
     * region standing under one. Only the last is read twice, and it is read twice because there are
     * two readings of it and not because anything read it again.
     */
    private static final List<Place> PLACES = List.of(
            read("standing on its own",
                    "let run (a, t) = Box { p = Pair { l = $A, r = a }, q = Amount(0) }\n"),
            read("beside a binding an expansion introduced",
                    "let run (a, t) = Box { p = Pair { l = bump(bump(a)), r = $A }, q = a }\n"),
            read("in the condition a conditional is decided by",
                    "let run (a, t) = Box { p = Pair { l = if $A.value > 3 then Amount(1)"
                            + " else Amount(2), r = a }, q = a }\n"),
            read("beside a conditional, in the region it is opened in",
                    "let run (a, t) = Box { p = Pair { l = if a.value > 3 then Amount(1)"
                            + " else Amount(2), r = $A }, q = a }\n"),
            read("in a branch of that conditional",
                    "let run (a, t) = Box { p = Pair { l = if a.value > 3 then Amount($A.value)"
                            + " else Amount(2), r = a }, q = a }\n"),
            read("in the condition of a conditional an arm stands over", """
                    let run (a, t) = Box
                        { p = Pair
                                { l = match t with
                                        | Lo -> if $A.value > 3 then Amount(1) else Amount(2)
                                        | Hi -> Amount(9)
                                , r = a
                                }
                        , q = a
                        }
                    """),
            read("in a branch of a conditional an arm stands over", """
                    let run (a, t) = Box
                        { p = Pair
                                { l = match t with
                                        | Lo -> if a.value > 3 then Amount($A.value) else Amount(2)
                                        | Hi -> Amount(9)
                                , r = a
                                }
                        , q = a
                        }
                    """),
            read("in an arm, with no conditional anywhere", """
                    let run (a, t) = Box
                        { p = match t with
                                | Lo -> Pair { l = $A, r = a }
                                | Hi -> Pair { l = Amount(9), r = a }
                        , q = a
                        }
                    """),
            readTwice("in an arm standing under a conditional", """
                    let run (a, t) = Box
                        { p = match t with
                                | Lo -> Pair { l = $A, r = a }
                                | Hi -> Pair { l = Amount(9), r = a }
                        , q = if a.value > 3 then Amount(1) else Amount(2)
                        }
                    """),
            readTwice("in an arm standing under a conditional written in that arm", """
                    let run (a, t) = Box
                        { p = match t with
                                | Lo -> Pair { l = if a.value > 3 then Amount(1) else Amount(2)
                                             , r = $A }
                                | Hi -> Pair { l = Amount(9), r = a }
                        , q = a
                        }
                    """));

    /** Every answer seeded while compiling {@code source}, one entry per seeding. */
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

    /** {@code answers} distinct answers were seeded over {@code source}, each of them
     * {@code readings} times. */
    private static void seeded(int answers, int readings, String source, String what) {
        List<Core> seeded = seededIn(source);
        Map<Core, Boolean> distinct = new IdentityHashMap<>();
        seeded.forEach(answer -> distinct.put(answer, true));
        assertEquals(answers, distinct.size(), "answers seeded over " + what);
        assertEquals(answers * readings, seeded.size(),
                "seedings of " + answers + " answers over " + what);
    }

    /**
     * Where an answer stands does not decide how often it is read, and how many readings of its
     * region there are does.
     *
     * <p>Read against a growing number of answers, so what is held is that the seedings follow the
     * answers one for one: a body of one answer read twice and a body of two read once are the same
     * two seedings, and only the slope tells them apart.
     */
    @Test
    void anAnswerIsReadOncePerReadingOfTheRegionItStandsIn() {
        for (Place place : PLACES) {
            for (int answers : List.of(1, 2, 4)) {
                seeded(answers, place.readings(),
                        DECLARATIONS + place.body().replace("$A", answers(answers)),
                        answers + " answers " + place.what());
            }
        }
    }

    /**
     * A body whose whole of it is one region: {@code depth} calls nested inside one another, with no
     * branch, no block and no binding between them to end the reading early.
     *
     * <p>Beside the places above rather than one of them, because it holds the other half. They vary
     * where an answer stands; this varies how far the reading runs to reach it, which is what came
     * out quadratic when every node standing over an answer read it again.
     */
    @Test
    void anAnswerIsReadOnceHoweverFarTheReadingRunsToReachIt() {
        for (int depth : List.of(1, 2, 4, 8, 16)) {
            String source = """
                    module demo exposing ( Amount, step, run )

                    data Amount = Int
                        invariant value >= 0

                    behavior step : (a: Amount) -> Amount
                        constructs Amount

                    let step (a) = Amount(a.value + 1)

                    behavior run : (a: Amount) -> Amount
                        constructs Amount

                    let run (a) = Amount(%s.value + 1)
                    """.formatted(answers(depth));
            seeded(depth, 1, source, "a body of " + depth + " nested calls");
        }
    }
}
