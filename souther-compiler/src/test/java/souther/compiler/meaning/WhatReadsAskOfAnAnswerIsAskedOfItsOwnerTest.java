package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.time.Duration;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * What an operation answers holds numbers of the input and other answers and nothing else, so what
 * a reader asks of one is asked of the positions it is made of, or is the same for every answer. A
 * reader that goes down the arguments itself goes down every path to a number, and in a chain of
 * calls each handed the one before it twice there are two to the depth of them.
 */
class WhatReadsAskOfAnAnswerIsAskedOfItsOwnerTest {

    private static final ValueName.Stdlib FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    private static final TermPath ELEMENT_LIST = TermPath.of("i").then("ys");

    /** Deep enough that two to the depth of it visits is out of reach. */
    private static final int DEEP = 60;

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

    private static <T> T promptly(java.util.concurrent.Callable<T> ask) {
        return assertTimeoutPreemptively(Duration.ofSeconds(10), ask::call);
    }

    @Test
    void whetherAnAnswerMayBeAnElementOfAnUnrelatedContainerIsAskedOfItsPositions() {
        DecisionSubject unrelated = new DecisionSubject.AnInput(ELEMENT_LIST);
        boolean shallow = comparing(chain(2)).mayTurnOnAnElementOf(unrelated);
        assertEquals(shallow, promptly(() -> comparing(chain(DEEP)).mayTurnOnAnElementOf(unrelated)));
        assertFalse(shallow);
    }

    @Test
    void whetherAnAnswerMayBeAnElementOfTheContainerItIsReadOffStillSaysSo() {
        Quantity ofTheElement = new DecisionAtom.OfTheInput(
                new NumericTerm.ValueOf(ELEMENT_LIST.element().then("p")));
        Quantity element = new Quantity.WhatAnOperationAnswers(FLOOR_MOD,
                List.of(chain(DEEP), ofTheElement));
        assertEquals(true, promptly(() -> comparing(element)
                .mayTurnOnAnElementOf(new DecisionSubject.AnInput(ELEMENT_LIST))));
    }

    @Test
    void whetherAStatementMovesWithANodeIsAskedOfTheAnswersPositions() {
        TermPath node = TermPath.of("i");
        boolean shallow = WrittenOfANode.movesWithIt(comparing(chain(2)), node, List.of());
        assertEquals(shallow,
                promptly(() -> WrittenOfANode.movesWithIt(comparing(chain(DEEP)), node, List.of())));
    }

    @Test
    void thePlacesAnAnswerIsReadOffAreCollectedOncePerPlace() {
        assertEquals(PositionsAStatementReads.ofANumber(chain(2)),
                promptly(() -> PositionsAStatementReads.ofANumber(chain(DEEP))));
        assertEquals(PositionsAStatementReads.everyPlaceOf(comparing(chain(2))),
                promptly(() -> PositionsAStatementReads.everyPlaceOf(comparing(chain(DEEP)))));
    }

    @Test
    void aNumberCarriedByAWalkIsNeverInAnAnswer() {
        Quantity.HowManyCarried carried = new Quantity.HowManyCarried(ACarriedValue.made());
        assertFalse(promptly(() -> carried.isIn(chain(DEEP))));
    }

    @Test
    void anAnswerAHundredThousandCallsDeepIsReadWithoutOverflowingTheStack() {
        Quantity.WhatAnOperationAnswers deep = (Quantity.WhatAnOperationAnswers) chain(100_000);
        assertEquals(1, promptly(deep::positionsItIsMadeOf).size());
        assertEquals(true, promptly(() -> deep.spelling().length() > 0));
        assertEquals(deep, promptly(() -> chain(100_000)));
        assertEquals(deep, promptly(() -> deep.rebuilt(input -> input)));
    }
}
