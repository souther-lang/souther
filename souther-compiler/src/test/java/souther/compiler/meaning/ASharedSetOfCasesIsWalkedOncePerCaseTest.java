package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Figure;
import souther.compiler.partition.CompositionBudget;
import souther.test.Allocated;
import souther.test.Growth;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.SequencedMap;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.Callable;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases a line decides in are a graph: the state a choice leaves is one value every way to it
 * shares, so the ways of choosing are the product of the choices and the cases that hold them are
 * their sum. Every question asked of all of them, every comparison and every rendering, costs a
 * visit to each case and not a visit to each way of choosing, and what it makes of a case does not
 * grow with the ways that lead to it.
 *
 * <p>Put to graphs that share in each way the cases allow: sharing a rest under one of several
 * alternatives, under one group of several held together, and both at once. What a question costs
 * is the memory it allocates, which a walk makes of each visit and which does not depend on how
 * fast the machine is. A graph of ten steps is asked for what it allocates against one of five:
 * a visit to each case doubles it, a rendering that copies what it has written so far quadruples
 * it, and a visit to each way of choosing makes it at least thirty-two times what it was.
 */
class ASharedSetOfCasesIsWalkedOncePerCaseTest {

    private static final int STEPS = 10;

    /** The smaller of the two sizes a cost is compared at, and the larger is twice it. */
    private static final int SMALLER = 5;

    private static Proposition truth(String at) {
        return new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of(at)), true);
    }

    private static DecidingCase.Cases one(Proposition condition) {
        return new DecidingCase.Cases.One(condition);
    }

    /** At each of {@code steps} parts the case holds or fails it and goes on to the same rest. */
    private static DecidingCase.Cases sharingTheRest(int steps, DecidingCase.Cases end) {
        DecidingCase.Cases rest = end;
        for (int part = 0; part < steps; part++) {
            Proposition holds = truth("part" + part);
            rest = new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.Together(List.of(one(holds), rest)),
                    new DecidingCase.Cases.Together(List.of(one(holds.denied()), rest))));
        }
        return rest;
    }

    /** At each of {@code steps} steps the same case is held twice together. */
    private static DecidingCase.Cases heldTwice(int steps, DecidingCase.Cases end) {
        DecidingCase.Cases rest = end;
        for (int step = 0; step < steps; step++) {
            rest = new DecidingCase.Cases.Together(List.of(rest, rest));
        }
        return rest;
    }

    /** Both: a group of a part and a rest held together, under each of two alternatives, and the
     *  rest the same group twice. */
    private static DecidingCase.Cases heldTwiceUnderAlternatives(int steps,
                                                                 DecidingCase.Cases end) {
        DecidingCase.Cases rest = end;
        for (int step = 0; step < steps; step++) {
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
                    : DecidingCase.Cases.together(held));
            if (withCasesNobodyTookApart && dice.nextInt(15) == 0) {
                before.add(NOT_TAKEN_APART);
            }
        }
        return before.getLast();
    }

    private static final DecidingCase.Cases.NotTakenApart NOT_TAKEN_APART =
            new DecidingCase.Cases.NotTakenApart(
                    CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.reached());

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
        asked.put("structuralWays", () -> cases.structuralWays(CaseCount.WAYS_A_COUNT_IS_HELD_TO));
        asked.put("eachSaid", () -> cases.eachSaid(DecidingCase.Cases.One::new));
        asked.put("notTakenApartAt", cases::notTakenApartAt);
        asked.put("references", cases::references);
        return asked;
    }

    /** What asking {@code ask} allocates on this thread. */
    private static long allocatedBy(Callable<?> ask) {
        return Allocated.by(() -> {
            try {
                assertTrue(ask.call() != null);
            } catch (Exception failed) {
                throw new IllegalStateException(failed);
            }
        });
    }

    /**
     * That what {@code asked} allocates at {@link #STEPS} steps is no more than what it allocates at
     * {@link #SMALLER} steps scaled up by the steps, with room for the part that does not scale.
     * Each size is asked of a graph of its own made beforehand, and one is asked first to leave
     * what the first ask loads out of the count.
     */
    private static void assertCostGrowsWithTheCasesAndNotTheWays(String what,
                                                                IntFunction<Callable<?>> asked) {
        allocatedBy(asked.apply(SMALLER));
        SequencedMap<Integer, Long> bySize = new LinkedHashMap<>();
        bySize.put(SMALLER, allocatedBy(asked.apply(SMALLER)));
        bySize.put(STEPS, allocatedBy(asked.apply(STEPS)));
        try {
            Growth.eachAtMost(bySize, 8, 1);
        } catch (AssertionError grew) {
            throw new AssertionError(what + ": " + grew.getMessage(), grew);
        }
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

    private static Map<String, DecidingCase.Cases> sharing(int steps) {
        DecidingCase.Cases end = one(truth("end"));
        DecidingCase.Cases choice = new DecidingCase.Cases.EachOf(List.of(one(truth("a")),
                one(truth("b"))));
        Map<String, DecidingCase.Cases> out = new TreeMap<>();
        out.put("a rest under each of two alternatives", sharingTheRest(steps, end));
        out.put("the same case held twice together", heldTwice(steps, end));
        out.put("the same choice held twice together", heldTwice(steps, choice));
        out.put("a rest held twice under each of two alternatives",
                heldTwiceUnderAlternatives(steps, end));
        out.put("cases nobody took apart, held twice together", heldTwice(steps, NOT_TAKEN_APART));
        return out;
    }

    @Test
    void everyQuestionCostsAVisitToEachCaseAndNotToEachWayOfChoosing() throws Exception {
        for (String shape : sharing(STEPS).keySet()) {
            for (String question : askedOf(one(truth("end"))).keySet()) {
                assertCostGrowsWithTheCasesAndNotTheWays(question + " of " + shape,
                        steps -> askedOf(sharing(steps).get(shape)).get(question));
            }
            assertCostGrowsWithTheCasesAndNotTheWays(
                    "putting what every case holds first, of " + shape, steps -> {
                        DecidingCase.Cases cases = sharing(steps).get(shape);
                        return () -> CasesOfALineAsked.heldFirst(cases);
                    });
        }
    }

    /** What is made of the cases is no larger than the cases: one case more for each case, however
     *  many ways lead to it. */
    @Test
    void whatIsMadeOfSharedCasesIsAsManyCasesAsThereAre() {
        for (Map.Entry<String, DecidingCase.Cases> shape : sharing(STEPS).entrySet()) {
            int cases = shape.getValue().references().size();
            int ordered = CasesOfALineAsked.heldFirst(shape.getValue()).references().size();
            assertTrue(ordered <= 2 * cases + 2, shape.getKey() + ": " + cases + " cases are put "
                    + "in order as " + ordered);
        }
    }

    /** Whatever the graph, every question is answered of it; that it is answered in what grows with
     *  its cases is held by the shapes above, which are the ones that tell the two apart. */
    @Test
    void graphsDrawnAtRandomAreAskedEveryQuestion() throws Exception {
        Random dice = new Random(2680);
        for (int round = 0; round < 200; round++) {
            DecidingCase.Cases cases = drawn(dice, 6 + dice.nextInt(12), round % 3 == 0);
            for (Callable<?> each : askedOf(cases).values()) {
                each.call();
            }
            CasesOfALineAsked.heldFirst(cases);
            assertTrue(!cases.toString().isEmpty(), "writing the graph drawn at round " + round);
        }
    }

    @Test
    void theFiguresCasesWereNeverTakenApartAtAreFoundBeneathTheSharedRest() {
        Set<Figure.Budget> figures = sharingTheRest(STEPS, NOT_TAKEN_APART).notTakenApartAt();
        assertEquals(Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.reached()), figures);
        assertEquals(Set.of(), sharingTheRest(STEPS, one(truth("end"))).notTakenApartAt());
    }

    @Test
    void whereTheWaysAreManyTheConditionIsNotWrittenAndWhereTheyAreFewItIs() {
        DecidingCase.Cases shared = sharingTheRest(STEPS, one(truth("end")));
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
    void twoGraphsOfTheSameCasesAreEqualAndTwoThatDifferAtTheEndAreNot() throws Exception {
        DecidingCase.Cases one = sharingTheRest(STEPS, one(truth("end")));
        DecidingCase.Cases other = sharingTheRest(STEPS, one(truth("end")));
        assertTrue(one != other);
        assertEquals(one, other);
        assertEquals(one.hashCode(), other.hashCode());
        assertNotEquals(one, sharingTheRest(STEPS, one(truth("another end"))));
        assertNotEquals(one, sharingTheRest(STEPS, NOT_TAKEN_APART));
        assertEquals(heldTwice(STEPS, one(truth("end"))), heldTwice(STEPS, one(truth("end"))));
        assertEquals(DecidingCase.alone(truth("said")), DecidingCase.alone(truth("said")));
        assertEquals(new DecidingCase(truth("said"), one), new DecidingCase(truth("said"), other));

        assertCostGrowsWithTheCasesAndNotTheWays("comparing graphs of the same cases", steps -> {
            DecidingCase.Cases left = heldTwiceUnderAlternatives(steps, one(truth("end")));
            DecidingCase.Cases right = heldTwiceUnderAlternatives(steps, one(truth("end")));
            return () -> left.equals(right) && left.hashCode() == right.hashCode();
        });
    }

    @Test
    void theCasesAreWrittenOutOncePerCase() throws Exception {
        String written = sharingTheRest(STEPS, one(truth("end"))).toString();
        assertTrue(written.contains("#"), "a case more than one holds is written by its number");

        assertCostGrowsWithTheCasesAndNotTheWays("writing the cases out", steps -> {
            DecidingCase.Cases cases = sharingTheRest(steps, one(truth("end")));
            return cases::toString;
        });
    }

    @Test
    void theStepsRunningOutAskForTheFiguresOfTheCasesLeftOnceEach() throws Exception {
        for (DecidingCase.Cases cases : List.of(sharingTheRest(STEPS, NOT_TAKEN_APART),
                heldTwice(STEPS, NOT_TAKEN_APART),
                heldTwiceUnderAlternatives(STEPS, NOT_TAKEN_APART))) {
            CasesOfALineAsked.Found found = CasesOfALineAsked.casesOf(
                    new DecidingCase(truth("said"), cases),
                    _ -> CasesOfALineAsked.Crossing.MAY_CROSS);
            assertTrue(found.notWorkedOut()
                            .contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.reached()),
                    found.notWorkedOut().toString());
        }
        assertCostGrowsWithTheCasesAndNotTheWays("asking the cases left for their figures",
                steps -> {
                    DecidingCase said = new DecidingCase(truth("said"),
                            heldTwiceUnderAlternatives(steps, NOT_TAKEN_APART));
                    return () -> CasesOfALineAsked.casesOf(said,
                            _ -> CasesOfALineAsked.Crossing.MAY_CROSS);
                });
    }

    @Test
    void moreWaysOfChoosingThanAreTakenApartAskForTheFiguresOfTheCasesOnceEach() throws Exception {
        for (DecidingCase.Cases cases : List.of(sharingTheRest(STEPS, NOT_TAKEN_APART),
                heldTwiceUnderAlternatives(STEPS, NOT_TAKEN_APART))) {
            CasesOfALineAsked.Atoms<Boolean> found = CasesOfALineAsked.atomsOf(
                    new DecidingCase(truth("said"), cases), _ -> true);
            assertTrue(found.each().isEmpty());
            assertTrue(found.notWorkedOut()
                    .contains(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.reached()));
            assertTrue(found.notWorkedOut()
                    .contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.reached()));
        }
        assertCostGrowsWithTheCasesAndNotTheWays("taking the cases apart for their figures",
                steps -> {
                    DecidingCase said = new DecidingCase(truth("said"),
                            heldTwiceUnderAlternatives(steps, NOT_TAKEN_APART));
                    return () -> CasesOfALineAsked.atomsOf(said, _ -> true);
                });
    }
}
