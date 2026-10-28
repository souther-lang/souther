package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.time.Duration;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.Callable;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The cases a line decides in are a graph: the state a choice leaves is one value every way to it
 * shares, so the ways of choosing are the product of the choices and the cases that hold them are
 * their sum. Every question asked of all of them, every comparison and every rendering, costs a
 * visit to each case and not a visit to each way of choosing.
 *
 * <p>Put to cases that share their rest at every step of sixty-four, whose ways of choosing are
 * past anything that can be walked, with a time to stop a walk that is one way at a time.
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

    private static final DecidingCase.Cases.NotTakenApart NOT_TAKEN_APART =
            new DecidingCase.Cases.NotTakenApart(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN);

    /** Each question the cases are asked, so that a new one is put to this test with it. */
    private static final Map<String, Callable<?>> ASKED = askedOf(sharingTheRest(one(truth("end"))));

    private static Map<String, Callable<?>> askedOf(DecidingCase.Cases cases) {
        Map<String, Callable<?>> asked = new TreeMap<>();
        asked.put("fold", () -> cases.fold(new DecidingCase.Cases.Fold<Integer>() {
            @Override
            public Integer one(DecidingCase.Cases.One one) {
                return 1;
            }

            @Override
            public Integer eachOf(List<Integer> alternatives) {
                return alternatives.stream().mapToInt(Integer::intValue).sum() + 1;
            }

            @Override
            public Integer together(List<Integer> factors) {
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
        assertEquals(new TreeSet<>(ASKED.keySet()), answered,
                "a question the cases answer is walked once per case, and asked here");
    }

    @Test
    void everyQuestionCostsAVisitToEachCaseAndNotToEachWayOfChoosing() throws Exception {
        for (Map.Entry<String, Callable<?>> each : ASKED.entrySet()) {
            Object answer = assertTimeoutPreemptively(LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                    () -> each.getValue().call(), each.getKey());
            assertTrue(answer != null, each.getKey());
        }
        DecidingCase.Cases cases = sharingTheRest(one(truth("end")));
        assertEquals(1001L, cases.waysOfChoosing(1000));
        assertEquals(Optional.empty(), cases.holdingInSome(1000),
                "as long as there are ways of choosing, and so not written");
    }

    /** Where there are few ways of choosing the condition is written, and is the same whichever
     *  way the cases are held: shared or written out. */
    @Test
    void whereTheWaysAreFewTheConditionIsWrittenAsTheyWereTakenApart() {
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
    void theFiguresCasesWereNeverTakenApartAtAreFoundBeneathTheSharedRest() {
        Set<CompositionBudget> figures = assertTimeoutPreemptively(
                LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                () -> sharingTheRest(NOT_TAKEN_APART).notTakenApartAt());
        assertEquals(Set.of(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN), figures);
        assertEquals(Set.of(), sharingTheRest(one(truth("end"))).notTakenApartAt());
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
        DecidingCase said = new DecidingCase(truth("said"), sharingTheRest(NOT_TAKEN_APART));
        CasesOfALineAsked.Found found = assertTimeoutPreemptively(
                LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                () -> CasesOfALineAsked.casesOf(said, _ -> true));
        assertTrue(found.notWorkedOut().contains(CompositionBudget.CASES_A_LINE_IS_ASKED_IN),
                found.notWorkedOut().toString());
        assertTrue(found.notWorkedOut().contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN),
                found.notWorkedOut().toString());
    }

    @Test
    void moreWaysOfChoosingThanAreTakenApartAskForTheFiguresOfTheCasesOnceEach() {
        DecidingCase said = new DecidingCase(truth("said"), sharingTheRest(NOT_TAKEN_APART));
        CasesOfALineAsked.Atoms<Boolean> found = assertTimeoutPreemptively(
                LONG_ENOUGH_FOR_A_VISIT_TO_EACH_CASE,
                () -> CasesOfALineAsked.atomsOf(said, _ -> true));
        assertTrue(found.each().isEmpty());
        assertTrue(found.notWorkedOut()
                .contains(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));
        assertTrue(found.notWorkedOut().contains(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN));
        assertFalse(Arrays.asList(CompositionBudget.values()).isEmpty());
    }
}
