package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.Callable;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases a line decides in are a graph: the state a choice leaves is one value every way to it
 * shares, so the ways of choosing are the product of the choices and the cases that hold them are
 * their sum. Every question asked of all of them, every comparison and every rendering, costs a
 * visit to each case and not a visit to each way of choosing, and what it makes of a case does not
 * grow with the ways that lead to it.
 *
 * <p>Put to graphs that share in each way the cases allow, with a time to stop a walk that is one
 * way at a time or an answer that is written once for each: sharing a rest under one of several
 * alternatives, under one group of several held together, and both at once, at sixty-four steps
 * whose ways of choosing are past anything that can be walked, and to graphs drawn at random.
 */
class ASharedSetOfCasesIsWalkedOncePerCaseTest {

    private static final int STEPS = 64;

    private static final Duration LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE = Duration.ofSeconds(20);

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static DecidingCase.Cases one(Proposition condition) {
        return new DecidingCase.Cases.One(condition);
    }

    /** At each of {@link #STEPS} parts the case holds or fails it and goes on to the same rest. */
    private static DecidingCase.Cases sharingTheRest(DecidingCase.Cases end) {
        DecidingCase.Cases rest = end;
        for (int part = 0; part < STEPS; part++) {
            Proposition holds = truth("part" + part);
            rest = new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.Together(List.of(one(holds), rest)),
                    new DecidingCase.Cases.Together(List.of(one(holds.denied()), rest))));
        }
        return rest;
    }

    /** At each of {@link #STEPS} steps the same case is held twice together. */
    private static DecidingCase.Cases heldTwice(DecidingCase.Cases end) {
        DecidingCase.Cases rest = end;
        for (int step = 0; step < STEPS; step++) {
            rest = new DecidingCase.Cases.Together(List.of(rest, rest));
        }
        return rest;
    }

    /** Both: a group of a part and a rest held together, under each of two alternatives, and the
     *  rest the same group twice. */
    private static DecidingCase.Cases heldTwiceUnderAlternatives(DecidingCase.Cases end) {
        DecidingCase.Cases rest = end;
        for (int step = 0; step < STEPS; step++) {
            DecidingCase.Cases twice = new DecidingCase.Cases.Together(List.of(rest, rest));
            rest = new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.Together(List.of(one(truth("on" + step)), twice)),
                    new DecidingCase.Cases.Together(List.of(one(truth("off" + step)), twice))));
        }
        return rest;
    }

    /** Graphs of {@code nodes} cases each held by a few of the ones before it, at random. */
    private static DecidingCase.Cases drawn(Random dice, int nodes, boolean withCasesNobodyTookApart) {
        List<DecidingCase.Cases> before = new ArrayList<>();
        for (int at = 0; at < 3; at++) {
            before.add(one(truth("leaf" + at)));
        }
        for (int at = 0; at < nodes; at++) {
            List<DecidingCase.Cases> held = new ArrayList<>();
            int howMany = dice.nextInt(4);
            for (int i = 0; i < howMany; i++) {
                int back = dice.nextInt(3) == 0 ? dice.nextInt(before.size())
                        : before.size() - 1 - dice.nextInt(Math.min(3, before.size()));
                held.add(before.get(back));
            }
            before.add(dice.nextBoolean() ? new DecidingCase.Cases.EachOf(held)
                    : new DecidingCase.Cases.Together(held));
            if (withCasesNobodyTookApart && dice.nextInt(15) == 0) {
                before.add(NOT_TAKEN_APART);
            }
        }
        return before.getLast();
    }

    private static final DecidingCase.Cases.NotTakenApart NOT_TAKEN_APART =
            new DecidingCase.Cases.NotTakenApart(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN);

    /** Each question the cases are asked, so that a new one is put to this test with it. */
    private static Map<String, Callable<?>> askedOf(DecidingCase.Cases cases) {
        Map<String, Callable<?>> asked = new TreeMap<>();
        asked.put("fold", () -> cases.fold(new DecidingCase.Cases.Fold<Integer>() {
            @Override
            public Integer one(DecidingCase.Cases.One one) {
                return 1;
            }

            @Override
            public Integer eachOf(DecidingCase.Cases.EachOf node, List<Integer> alternatives) {
                return alternatives.stream().mapToInt(Integer::intValue).sum() + 1;
            }

            @Override
            public Integer together(DecidingCase.Cases.Together node, List<Integer> factors) {
                return factors.stream().mapToInt(Integer::intValue).sum() + 1;
            }

            @Override
            public Integer notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return 1;
            }
        }));
        asked.put("holdingInSome", () -> cases.holdingInSome(1000));
        asked.put("waysOfChoosing", () -> cases.waysOfChoosing(1000));
        asked.put("eachSaid", () -> cases.eachSaid(DecidingCase.Cases.One::new));
        asked.put("notTakenApartAt", cases::notTakenApartAt);
        asked.put("references", cases::references);
        return asked;
    }

    /** The questions the cases answer are these and no others, and each is asked of the shared
     *  cases below: a question added is put here with the way it is asked. */
    @Test
    void everyQuestionTheCasesAnswerIsAskedOfTheSharedOnes() {
        Set<String> answered = new TreeSet<>();
        for (Method each : DecidingCase.Cases.class.getDeclaredMethods()) {
            if (Modifier.isPublic(each.getModifiers()) && !Modifier.isStatic(each.getModifiers())
                    && !each.isSynthetic()) {
                answered.add(each.getName());
            }
        }
        assertEquals(new TreeSet<>(askedOf(one(truth("end"))).keySet()), answered,
                "a question the cases answer is walked once per case, and asked here");
    }

    private static Map<String, DecidingCase.Cases> sharing() {
        DecidingCase.Cases end = one(truth("end"));
        DecidingCase.Cases choice = new DecidingCase.Cases.EachOf(List.of(one(truth("a")),
                one(truth("b"))));
        Map<String, DecidingCase.Cases> out = new TreeMap<>();
        out.put("a rest under each of two alternatives", sharingTheRest(end));
        out.put("the same case held twice together", heldTwice(end));
        out.put("the same choice held twice together", heldTwice(choice));
        out.put("a rest held twice under each of two alternatives",
                heldTwiceUnderAlternatives(end));
        out.put("cases nobody took apart, held twice together", heldTwice(NOT_TAKEN_APART));
        return out;
    }

    @Test
    void everyQuestionCostsAVisitToEachCaseAndNotToEachWayOfChoosing() throws Exception {
        for (Map.Entry<String, DecidingCase.Cases> shape : sharing().entrySet()) {
            for (Map.Entry<String, Callable<?>> each : askedOf(shape.getValue()).entrySet()) {
                Object answer = assertTimeoutPreemptively(LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                        () -> each.getValue().call(), each.getKey() + " of " + shape.getKey());
                assertTrue(answer != null, each.getKey());
            }
            Object ordered = assertTimeoutPreemptively(LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                    () -> CasesOfALineAsked.heldFirst(shape.getValue()),
                    "putting what every case holds first, of " + shape.getKey());
            assertTrue(ordered != null);
        }
    }

    /** What is made of the cases is no larger than the cases: one case more for each case, however
     *  many ways lead to it. */
    @Test
    void whatIsMadeOfSharedCasesIsAsManyCasesAsThereAre() {
        for (Map.Entry<String, DecidingCase.Cases> shape : sharing().entrySet()) {
            int cases = shape.getValue().references().size();
            int ordered = assertTimeoutPreemptively(LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                    () -> CasesOfALineAsked.heldFirst(shape.getValue()).references().size());
            assertTrue(ordered <= 2 * cases + 2, shape.getKey() + ": " + cases + " cases are put "
                    + "in order as " + ordered);
        }
    }

    @Test
    void graphsDrawnAtRandomAreAskedEveryQuestionInTimeBoundByTheirCases() throws Exception {
        Random dice = new Random(2680);
        for (int round = 0; round < 200; round++) {
            DecidingCase.Cases cases = drawn(dice, 12 + dice.nextInt(40), round % 3 == 0);
            for (Map.Entry<String, Callable<?>> each : askedOf(cases).entrySet()) {
                assertTimeoutPreemptively(Duration.ofSeconds(5), () -> each.getValue().call(),
                        each.getKey() + " of the graph drawn at round " + round);
            }
            assertTimeoutPreemptively(Duration.ofSeconds(5), () -> CasesOfALineAsked.heldFirst(cases),
                    "putting what every case holds first, at round " + round);
            assertTimeoutPreemptively(Duration.ofSeconds(5), () -> cases.toString(),
                    "writing the graph drawn at round " + round);
        }
    }

    @Test
    void theFiguresCasesWereNeverTakenApartAtAreFoundBeneathTheSharedRest() {
        Set<CompositionBudget> figures = assertTimeoutPreemptively(
                LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                () -> sharingTheRest(NOT_TAKEN_APART).notTakenApartAt());
        assertEquals(Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN), figures);
        assertEquals(Set.of(), sharingTheRest(one(truth("end"))).notTakenApartAt());
    }

    @Test
    void whereTheWaysAreManyTheConditionIsNotWrittenAndWhereTheyAreFewItIs() {
        DecidingCase.Cases shared = sharingTheRest(one(truth("end")));
        assertEquals(1001L, shared.waysOfChoosing(1000));
        assertEquals(Optional.empty(), shared.holdingInSome(1000),
                "as long as there are ways of choosing, and so not written");

        DecidingCase.Cases cases = new DecidingCase.Cases.EachOf(List.of(
                new DecidingCase.Cases.Together(List.of(one(truth("a")), one(truth("c")))),
                new DecidingCase.Cases.Together(List.of(one(truth("b")), one(truth("c"))))));
        assertEquals(Optional.of(Proposition.any(List.of(
                        Proposition.all(List.of(truth("a"), truth("c"))),
                        Proposition.all(List.of(truth("b"), truth("c")))))),
                cases.holdingInSome(1000));
        assertEquals(Optional.empty(), cases.holdingInSome(1));
    }

    @Test
    void twoGraphsOfTheSameCasesAreEqualAndTwoThatDifferAtTheEndAreNot() {
        assertTimeoutPreemptively(LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE, () -> {
            DecidingCase.Cases one = sharingTheRest(one(truth("end")));
            DecidingCase.Cases other = sharingTheRest(one(truth("end")));
            assertTrue(one != other);
            assertEquals(one, other);
            assertEquals(one.hashCode(), other.hashCode());
            assertNotEquals(one, sharingTheRest(one(truth("another end"))));
            assertNotEquals(one, sharingTheRest(NOT_TAKEN_APART));
            assertEquals(heldTwice(one(truth("end"))), heldTwice(one(truth("end"))));
            assertEquals(DecidingCase.alone(truth("said")), DecidingCase.alone(truth("said")));
            assertEquals(new DecidingCase(truth("said"), one),
                    new DecidingCase(truth("said"), other));
        });
    }

    @Test
    void theCasesAreWrittenOutOncePerCase() {
        String written = assertTimeoutPreemptively(LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                () -> sharingTheRest(one(truth("end"))).toString());
        assertTrue(written.length() < 100_000, "as long as the cases are many: " + written.length());
        assertTrue(written.contains("#"), "a case more than one holds is written by its number");
    }

    @Test
    void theStepsRunningOutAskForTheFiguresOfTheCasesLeftOnceEach() {
        for (DecidingCase.Cases cases : List.of(sharingTheRest(NOT_TAKEN_APART),
                heldTwice(NOT_TAKEN_APART), heldTwiceUnderAlternatives(NOT_TAKEN_APART))) {
            DecidingCase said = new DecidingCase(truth("said"), cases);
            CasesOfALineAsked.Found found = assertTimeoutPreemptively(
                    LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                    () -> CasesOfALineAsked.casesOf(said, _ -> true));
            assertTrue(found.notWorkedOut().contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN),
                    found.notWorkedOut().toString());
        }
    }

    @Test
    void moreWaysOfChoosingThanAreTakenApartAskForTheFiguresOfTheCasesOnceEach() {
        for (DecidingCase.Cases cases : List.of(sharingTheRest(NOT_TAKEN_APART),
                heldTwiceUnderAlternatives(NOT_TAKEN_APART))) {
            DecidingCase said = new DecidingCase(truth("said"), cases);
            CasesOfALineAsked.Atoms<Boolean> found = assertTimeoutPreemptively(
                    LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                    () -> CasesOfALineAsked.atomsOf(said, _ -> true));
            assertTrue(found.each().isEmpty());
            assertTrue(found.notWorkedOut()
                    .contains(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));
            assertTrue(found.notWorkedOut()
                    .contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN));
        }
    }
}
