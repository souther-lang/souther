package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That an operation's answer is a piece of each element of a list put end to end is held to the
 * signature, and proved of the body: which value each way of the walk's step puts, and on which
 * way, and not only that every way puts something after what it carries.
 */
class AListPutTogetherOfAPieceOfEachElementIsProvedOfTheBodyTest {

    private static final ValueName MAP = ValueName.Stdlib.operation("List", "map");
    private static final ValueName FILTER = ValueName.Stdlib.operation("List", "filter");
    private static final ValueName FLAT_MAP = ValueName.Stdlib.operation("List", "flatMap");
    private static final ValueName LENGTH = ValueName.Stdlib.operation("List", "length");

    private static final String SHIPPED_MAP = "List.fold((acc, x) -> acc ++ [f(x)], [], xs)";
    private static final String SHIPPED_FILTER =
            "List.fold((acc, x) -> if keep(x) then acc ++ [x] else acc, [], xs)";
    private static final String SHIPPED_FLAT_MAP = "List.fold((acc, x) -> acc ++ f(x), [], xs)";

    /** Control: what the library ships is proved, each with the piece it makes. */
    @Test
    void theLibraryAsShippedPutsTogetherWhatItIsSaidTo() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertEquals(PieceOfAnElement.THE_CLOSURES_ANSWER, facts.assembles(MAP).piece());
        assertEquals(PieceOfAnElement.THE_ELEMENT_WHERE_IT_HOLDS, facts.assembles(FILTER).piece());
        assertEquals(PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS, facts.assembles(FLAT_MAP).piece());
        assertEquals(List.of(), unproved(facts), "nothing stated of the three is left open");
    }

    /**
     * How many an operation putting a list together of pieces answers is what the piece says it
     * is: one for each element, as many as the closure holds of, or what the closure's answers
     * hold added up. The law of the size is another observation and proved by a proof of its own;
     * this holds the two statements about one answer to each other, so neither is changed alone.
     */
    @Test
    void howManyItAnswersIsWhatThePieceSays() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        for (ValueName operation : List.of(MAP, FILTER, FLAT_MAP)) {
            BoundOperationFacts.Assembled assembled = facts.assembles(operation);
            DeclaredArgument source = assembled.source();
            LawSubject<DeclaredArgument> answered =
                    new LawSubject.WhatTheClosureAnswers<>(assembled.closure());
            LawNumber<DeclaredArgument> expected = switch (assembled.piece()) {
                case THE_CLOSURES_ANSWER -> new LawNumber.SizeOf<>(new LawSubject.Argument<>(source));
                case THE_ELEMENT_WHERE_IT_HOLDS -> new LawNumber.HowManyMeet<>(source,
                        new LawProposition.Observed<>(answered,
                                new SideAnswered(AnswerAspect.TRUTH, true)));
                case WHAT_THE_CLOSURE_ANSWERS -> new LawNumber.SumOver<>(source,
                        new LawNumber.SizeOf<>(answered));
            };
            BoundOperationFacts.Settled settled =
                    facts.settled(operation, OperationLaw.Observed.SIZE);
            assertTrue(settled instanceof BoundOperationFacts.Settled.ByALaw(
                            OperationLaw.Size<DeclaredArgument> size, var _)
                            && LinearForm.atom(expected).equals(size.unconditional()),
                    () -> operation + " is settled " + settled + ", and its piece says "
                            + expected);
        }
    }

    /**
     * A filter keeping what its closure does not hold of has the shape of one: every way of its
     * step keeps what it carries or puts the element after it.
     */
    @Test
    void aStepKeepingTheElementWhereTheClosureFailsIsNoFilter() {
        BoundOperationFacts facts = proved(SHIPPED_FILTER,
                "List.fold((acc, x) -> if keep(x) then acc else acc ++ [x], [], xs)");

        assertNull(facts.assembles(FILTER));
        assertEquals(List.of(FILTER), unproved(facts), "stated, and left unproved");
    }

    /** Putting the element on both ways is putting it whatever the closure answers. */
    @Test
    void aStepPuttingTheElementEitherWayIsNoFilter() {
        assertNull(proved(SHIPPED_FILTER,
                "List.fold((acc, x) -> if keep(x) then acc ++ [x] else acc ++ [x], [], xs)")
                .assembles(FILTER));
    }

    /** A piece put before what is carried is the reverse order. */
    @Test
    void aPiecePutInFrontIsNotPutEndToEnd() {
        assertNull(proved(SHIPPED_FLAT_MAP, "List.fold((acc, x) -> f(x) ++ acc, [], xs)")
                .assembles(FLAT_MAP));
    }

    /** What the closure answered, put twice, is as long as twice the answers and is not them. */
    @Test
    void aPiecePutTwiceIsNotThePiece() {
        assertNull(proved(SHIPPED_FLAT_MAP, "List.fold((acc, x) -> acc ++ f(x) ++ f(x), [], xs)")
                .assembles(FLAT_MAP));
    }

    /** Two answers put for each element are answers of the closure, and not one of each. */
    @Test
    void twoAnswersPutForEachElementAreNotOneOfEach() {
        assertNull(proved(SHIPPED_MAP, "List.fold((acc, x) -> acc ++ [f(x), f(x)], [], xs)")
                .assembles(MAP));
    }

    /** A piece is said of an operation that hands a closure the elements it is made of. */
    @Test
    void anOperationTakingNoClosureMakesNoPiece() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(LENGTH,
                        new OperationFact.AssemblesPieces(new ArgumentRef.At(0),
                                PieceOfAnElement.THE_CLOSURES_ANSWER))));
        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /** And of a closure answering what that piece is made of: a map's closure answers no truth. */
    @Test
    void aPieceTheClosureDoesNotAnswerIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(MAP,
                        new OperationFact.AssemblesPieces(new ArgumentRef.TheContainer(),
                                PieceOfAnElement.THE_ELEMENT_WHERE_IT_HOLDS))));
        assertTrue(e.getMessage().contains("List.map"), e.getMessage());
    }

    /** The operations a piece was stated of and not proved. */
    private static List<ValueName> unproved(BoundOperationFacts facts) {
        return facts.notProvedOfTheirBodies().stream()
                .filter(each -> each instanceof BoundOperationFact.AssemblesPieces)
                .map(each -> each.operation().operation())
                .toList();
    }

    private static List<OperationFacts.Declared> declarations(ValueName operation,
                                                              OperationFact with) {
        List<OperationFacts.Declared> declared = new ArrayList<>(OperationFacts.declarations());
        declared.add(new OperationFacts.Declared(operation, with));
        return declared;
    }

    /**
     * Control for the bodies below: the pieces alone, bound over the library as shipped, are
     * proved. What a body rewritten fails to be proved is then the rewriting's, and not the
     * other facts it was bound without.
     */
    @Test
    void thePiecesAloneAreProvedOfTheBodiesAsShipped() {
        BoundOperationFacts facts = OperationFactBinder.bindAll(StdlibLoader.load(text -> text),
                thePieces());
        assertEquals(PieceOfAnElement.THE_CLOSURES_ANSWER, facts.assembles(MAP).piece());
        assertEquals(PieceOfAnElement.THE_ELEMENT_WHERE_IT_HOLDS, facts.assembles(FILTER).piece());
        assertEquals(PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS, facts.assembles(FLAT_MAP).piece());
    }

    /**
     * The library as shipped with {@code shipped} written as {@code body}, the pieces proved of it.
     *
     * <p>The pieces alone. Proving every fact the language declares is most of what binding costs,
     * and what a rewritten body is or is not is a question about this one.
     */
    private static BoundOperationFacts proved(String shipped, String body) {
        Stdlib stdlib = StdlibLoader.load(text -> text.contains(shipped)
                ? text.replace(shipped, body) : text);
        return OperationFactBinder.bindAll(stdlib, thePieces());
    }

    /** What the language declares of a list put together of pieces, and nothing else. */
    private static List<OperationFacts.Declared> thePieces() {
        return OperationFacts.declarations().stream()
                .filter(each -> each.fact() instanceof OperationFact.AssemblesPieces)
                .toList();
    }
}
