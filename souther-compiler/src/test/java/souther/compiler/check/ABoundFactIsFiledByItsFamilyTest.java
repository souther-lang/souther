package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.KeptCalls;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the binding makes is filed by the family the arm was written in, and applied to a call of
 * the declaration it is about.
 *
 * <p>Two rules a reader below the binding stands on without checking. A kind of fact an operation
 * carries one of is filed once and a second is refused — a map written into keeps whichever arrived
 * last, and a reader would get an answer that depended on the order the declarations were written
 * in. And a bound argument names the declaration it is an argument of, so a call it is applied to
 * has to be a call of that declaration: a position is a number, and a number is right in any call
 * that takes enough arguments.
 */
class ABoundFactIsFiledByItsFamilyTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static final ValueName.Stdlib.Operation LIST_LENGTH =
            ValueName.Stdlib.operation("List", "length");

    private static final ValueName.Stdlib.Operation LIST_APPEND =
            ValueName.Stdlib.operation("List", "append");

    private static final ValueName.Stdlib.Operation LIST_REVERSE =
            ValueName.Stdlib.operation("List", "reverse");

    private static final ValueName.Stdlib.Operation LIST_DISTINCT =
            ValueName.Stdlib.operation("List", "distinct");

    /**
     * A kind an operation carries one of, declared twice, is refused where the bound facts are
     * collected.
     *
     * <p>Each declaration holds on its own — {@code List.length} does count what it holds — so
     * nothing about either is wrong where it is bound. What is wrong is the pair, and the pair is
     * seen where the facts are filed.
     */
    @Test
    void aSecondFactOfAKindAnOperationCarriesOneOfIsRefused() {
        List<OperationFacts.Declared> gained = new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(LIST_LENGTH,
                new OperationFact.AnswersANumberTakenOfTheOneValueItIsGiven(
                        new TakenAs.HowManyItHolds())));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), gained));

        assertTrue(refused.getMessage().contains("List.length"), refused.getMessage());
        assertTrue(refused.getMessage().contains("twice"), refused.getMessage());
    }

    /** And a kind an operation may carry several of is kept whole, in the order declared. */
    @Test
    void aKindAnOperationCarriesSeveralOfIsKeptWhole() {
        List<DeclaredArgument> noSmallerThan =
                DefaultBoundOperationFacts.get().resultIsNoSmallerThan(LIST_APPEND);
        assertEquals(List.of(0, 1),
                noSmallerThan.stream().map(DeclaredArgument::position).toList(),
                "`a ++ b` is as long as either half, which is two facts about one operation");
        for (DeclaredArgument each : noSmallerThan) {
            assertEquals(LIST_APPEND, each.of().operation(),
                    "and each names the declaration it is an argument of");
        }
    }

    /** A bound argument applied to a call of the declaration it is an argument of answers the
     *  expression standing there. */
    @Test
    void aBoundArgumentIsFoundInACallOfItsOwnDeclaration() {
        Core.PreservedCall reverse = KeptCalls.to(LIST_REVERSE, POS);
        DeclaredArgument from =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(LIST_REVERSE).from();

        assertSame(reverse.args().get(0), CallArguments.of(from, reverse));
    }

    /**
     * And applied to a call of another declaration it is refused, however many arguments that call
     * takes.
     *
     * <p>{@code List.distinct} takes one argument as {@code List.reverse} does, so the position is
     * in range and the answer would have been an expression, standing where the wrong declaration
     * put it. The argument knows what it is an argument of, and that is what is held.
     */
    @Test
    void aBoundArgumentAppliedToACallOfAnotherDeclarationIsRefused() {
        Core.PreservedCall distinct = KeptCalls.to(LIST_DISTINCT, POS);
        DeclaredArgument from =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(LIST_REVERSE).from();
        assertEquals(distinct.args().size(), from.of().arity(),
                "the premise: the two take as many arguments, so a position alone would answer");

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> CallArguments.of(from, distinct));
        assertTrue(refused.getMessage().contains("another declaration"), refused.getMessage());
        assertThrows(IllegalStateException.class,
                () -> CallArguments.replacedIn(from, distinct, distinct.args().get(0)),
                "and a rebuild is refused the same way");
    }

    /**
     * And the same for a reader holding the operation's name and its arguments rather than a kept
     * call — the runnable tree's call, an expansion — which asks the position through the same
     * check rather than reading it off the argument.
     */
    @Test
    void aBoundArgumentAskedForUnderAnotherOperationsNameIsRefused() {
        DeclaredArgument from =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(LIST_REVERSE).from();

        assertEquals(0, CallArguments.positionOf(from, LIST_REVERSE));
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> CallArguments.positionOf(from, LIST_DISTINCT));
        assertTrue(refused.getMessage().contains("another declaration"), refused.getMessage());
    }

    /** A bound argument outside its declaration's arity cannot be made at all. */
    @Test
    void aBoundArgumentOutsideTheDeclarationIsRefusedWhereItIsMade() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new DeclaredArgument(KeptCalls.declared(LIST_REVERSE), 1, Type.INT));
        assertTrue(refused.getMessage().contains("List.reverse"), refused.getMessage());
    }
}
