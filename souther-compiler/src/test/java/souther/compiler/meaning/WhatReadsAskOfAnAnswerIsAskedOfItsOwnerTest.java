package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;
import souther.test.Allocated;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation answers holds numbers of the input and other answers and nothing else, so what
 * a reader asks of one is asked of the positions it is made of, or is the same for every answer. A
 * reader that goes down the arguments itself goes down every path to a number, and in a chain of
 * calls each handed the one before it twice there are two to the depth of them.
 */
class WhatReadsAskOfAnAnswerIsAskedOfItsOwnerTest {

    private static final ValueName.Stdlib FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    private static final TermPath ELEMENT_LIST = TermPath.of("i").then("ys");

    /** Deep enough that a visit to each way down is four thousand and ninety-six, which is well
     *  past what a visit to each call comes to. */
    private static final int DEEP = 12;

    /** Half of {@link #DEEP}, which a visit to each way down makes sixty-four times as cheap. */
    private static final int HALF = DEEP / 2;

    private static DecisionAtom.OfTheInput input(String field) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("i").then(field)));
    }

    private static Quantity chain(int depth) {
        Quantity answer = input("x");
        for (int i = 0; i < depth; i++) {
            answer = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(answer, answer));
        }
        return answer;
    }

    private static Proposition comparing(Quantity quantity) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.of(0),
                Map.of(quantity, ExactRatio.ONE)), Rel.GT), true);
    }

    /**
     * That what {@code asked} allocates at {@link #DEEP} is no more than eight times what it
     * allocates at {@link #HALF}. A reader that goes down the calls once each allocates twice as
     * much, and one that goes down every way allocates sixty-four times as much. Each depth is
     * asked of a chain made beforehand, and one is asked first to leave what the first ask loads out
     * of the count.
     */
    private static void assertCostIsOfTheCallsAndNotTheWaysDown(IntFunction<Runnable> asked) {
        asked.apply(HALF).run();
        SequencedMap<Integer, Long> bySize = new LinkedHashMap<>();
        bySize.put(HALF, Allocated.by(asked.apply(HALF)));
        bySize.put(DEEP, Allocated.by(asked.apply(DEEP)));
        Growth.eachAtMost(bySize, 8, 1);
    }

    @Test
    void whetherAnAnswerMayBeAnElementOfAnUnrelatedContainerIsAskedOfItsPositions() {
        DecisionSubject unrelated = new DecisionSubject.AnInput(ELEMENT_LIST);
        boolean shallow = comparing(chain(2)).mayTurnOnAnElementOf(unrelated);
        assertEquals(shallow, comparing(chain(DEEP)).mayTurnOnAnElementOf(unrelated));
        assertFalse(shallow);

        assertCostIsOfTheCallsAndNotTheWaysDown(depth -> {
            Proposition compared = comparing(chain(depth));
            return () -> compared.mayTurnOnAnElementOf(unrelated);
        });
    }

    @Test
    void whetherAnAnswerMayBeAnElementOfTheContainerItIsReadOffStillSaysSo() {
        Quantity ofTheElement = new DecisionAtom.OfTheInput(
                new NumericTerm.ValueOf(ELEMENT_LIST.element().then("p")));
        Quantity element = new Quantity.WhatAnOperationAnswers(FLOOR_MOD,
                List.of(chain(DEEP), ofTheElement));
        assertEquals(true, comparing(element)
                .mayTurnOnAnElementOf(new DecisionSubject.AnInput(ELEMENT_LIST)));
    }

    @Test
    void whetherAStatementMovesWithANodeIsAskedOfTheAnswersPositions() {
        TermPath node = TermPath.of("i");
        boolean shallow = WrittenOfANode.movesWithIt(comparing(chain(2)), node, List.of());
        assertEquals(shallow, WrittenOfANode.movesWithIt(comparing(chain(DEEP)), node, List.of()));

        assertCostIsOfTheCallsAndNotTheWaysDown(depth -> {
            Proposition compared = comparing(chain(depth));
            return () -> WrittenOfANode.movesWithIt(compared, node, List.of());
        });
    }

    @Test
    void thePlacesAnAnswerIsReadOffAreCollectedOncePerPlace() {
        assertEquals(PositionsAStatementReads.ofANumber(chain(2)),
                PositionsAStatementReads.ofANumber(chain(DEEP)));
        assertEquals(PositionsAStatementReads.everyPlaceOf(comparing(chain(2))),
                PositionsAStatementReads.everyPlaceOf(comparing(chain(DEEP))));

        assertCostIsOfTheCallsAndNotTheWaysDown(depth -> {
            Quantity answer = chain(depth);
            return () -> PositionsAStatementReads.ofANumber(answer);
        });
        assertCostIsOfTheCallsAndNotTheWaysDown(depth -> {
            Proposition compared = comparing(chain(depth));
            return () -> PositionsAStatementReads.everyPlaceOf(compared);
        });
    }

    @Test
    void aNumberCarriedByAWalkIsNeverInAnAnswer() {
        Quantity.HowManyCarried carried = new Quantity.HowManyCarried(ACarriedValue.made());
        assertFalse(carried.isIn(chain(DEEP)));

        // Nothing a walk carries is in an answer, so the answer is not read at all: asked of a
        // chain, it allocates nothing, where a reader going down every way would allocate for each.
        Quantity answer = chain(DEEP);
        assertTrue(Allocated.byWhichMayBeNothing(() -> carried.isIn(answer)) < 1_000);
    }

    /**
     * Each call handed a number of its own as well as the call before it, so the n-th answer is
     * made of n numbers. What is held for the answer asked is its numbers, and not the numbers of
     * every answer it is made of. What is held is what is allocated: twice the calls is twice the
     * numbers held, and the numbers of every answer along the way would be four times.
     */
    @Test
    void theNumbersOfAChainThatTakesOneMoreEachCallAreHeldForTheAnswerAskedOnly() {
        int depth = 2_000;
        Quantity.WhatAnOperationAnswers top = takingOneMoreEachCall(depth);
        List<NumericTerm> numbers = top.positionsItIsMadeOf();
        assertEquals(depth, numbers.size());
        assertEquals(input("x0").term(), numbers.getFirst());
        assertEquals(input("x" + (depth - 1)).term(), numbers.getLast());

        takingOneMoreEachCall(depth).positionsItIsMadeOf();
        SequencedMap<Integer, Long> bySize = new LinkedHashMap<>();
        for (int calls : new int[] {depth, 2 * depth}) {
            Quantity.WhatAnOperationAnswers answer = takingOneMoreEachCall(calls);
            bySize.put(calls, Allocated.by(answer::positionsItIsMadeOf));
        }
        Growth.eachAtMost(bySize, 5, 2);
    }

    private static Quantity.WhatAnOperationAnswers takingOneMoreEachCall(int depth) {
        Quantity answer = input("x0");
        for (int i = 1; i < depth; i++) {
            answer = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(answer, input("x" + i)));
        }
        return (Quantity.WhatAnOperationAnswers) answer;
    }

    @Test
    void aChainOfCallsOfOneArgumentIsAskedOfTheOwnerInALoopFromTheInnermostOut() {
        ValueName.Stdlib negate = ValueName.Stdlib.operation("Int", "negate");
        Quantity answer = input("x");
        for (int i = 0; i < 100_000; i++) {
            answer = new Quantity.WhatAnOperationAnswers(i == 99_999 ? negate : FLOOR_MOD,
                    List.of(answer));
        }
        Quantity.WhatAnOperationAnswers.OfOneArgument chain =
                ((Quantity.WhatAnOperationAnswers) answer).chainOfOneArgument();
        assertEquals(input("x"), chain.from());
        assertEquals(100_000, chain.operations().size());
        assertEquals(FLOOR_MOD, chain.operations().getFirst());
        assertEquals(negate, chain.operations().getLast());
    }

    @Test
    void aChainOfOneArgumentStopsAtTheFirstCallOfAnyOtherNumber() {
        Quantity two = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(input("x"), input("y")));
        Quantity.WhatAnOperationAnswers outer =
                new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(two));
        Quantity.WhatAnOperationAnswers.OfOneArgument chain = outer.chainOfOneArgument();
        assertEquals(two, chain.from());
        assertEquals(List.of(FLOOR_MOD), chain.operations());
    }

    @Test
    void anAnswerAHundredThousandCallsDeepIsReadWithoutOverflowingTheStack() {
        Quantity.WhatAnOperationAnswers deep = (Quantity.WhatAnOperationAnswers) chain(100_000);
        assertEquals(1, deep.positionsItIsMadeOf().size());
        assertTrue(deep.spelling().length() > 0);
        assertEquals(deep, chain(100_000));
        assertEquals(deep, deep.rebuilt(input -> input));
    }
}
