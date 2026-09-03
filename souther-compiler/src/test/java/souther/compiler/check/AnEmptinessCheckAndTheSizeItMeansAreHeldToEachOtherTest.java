package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.KeptCalls;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An emptiness check is said to mean a size, and what makes that true is the two declarations.
 *
 * <p>A reader of this fact writes a call of the size where a call of the check stands, moving the
 * arguments across. Two operations of one argument each is not enough for that to say the same
 * thing: a check on strings and a length of lists agree on how many arguments they take and on
 * nothing else, and a call rewritten between them would stand for a declaration it does not fit
 * while satisfying everything a call is held to on its own.
 *
 * <p>So the second half is here and is about the pair. It is asked once, where the library is read,
 * and what comes back carries it — the reader that rewrites has nothing left to check.
 */
class AnEmptinessCheckAndTheSizeItMeansAreHeldToEachOtherTest {

    private static final ValueName LIST_IS_EMPTY = ValueName.Stdlib.operation("List", "isEmpty");

    @Test
    void theOnesTheLanguageDeclaresAreHeld() {
        assertFalse(OperationFactBinder.bindAll(DefaultStdlib.get())
                        .meansTheSameAsASizeOfNought().isEmpty(),
                "nothing is declared to mean a size, so the rules below saw nothing");
    }

    /**
     * Two unary operations whose arguments are of different shapes are refused.
     *
     * <p>The one a call being held to its own declaration cannot catch: both take one argument, so
     * a call of either stands, and the rewrite between them is what is wrong.
     */
    @Test
    void aSizeOfSomethingElseIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(ValueName.Stdlib.operation("String", "isEmpty"),
                        ValueName.Stdlib.operation("List", "length")));

        assertTrue(e.getMessage().contains("String.isEmpty"), e.getMessage());
        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /** And that those two are each unary, so what the refusal above found is the shape. */
    @Test
    void andBothOfThoseTakeOneArgument() {
        assertEquals(1, KeptCalls
                .signature(ValueName.Stdlib.operation("String", "isEmpty")).params().size());
        assertEquals(1, KeptCalls
                .signature(ValueName.Stdlib.operation("List", "length")).params().size());
    }

    /** What is named as the size has to answer a number: it is what a rewrite compares to nought. */
    @Test
    void aSizeThatAnswersNoNumberIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(LIST_IS_EMPTY, ValueName.Stdlib.operation("List", "reverse")));

        assertTrue(e.getMessage().contains("List.reverse"), e.getMessage());
    }

    /** And what says it is an emptiness check has to answer a truth. */
    @Test
    void aCheckThatAnswersNoTruthIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(ValueName.Stdlib.operation("List", "length"),
                        ValueName.Stdlib.operation("List", "length")));

        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /**
     * One operation declared to mean two sizes is refused rather than answered with the last.
     *
     * <p>Both would be sizes it means, so neither is wrong where it is held — and what a call of the
     * check is rewritten to would depend on the order the declarations are written in.
     */
    @Test
    void anOperationDeclaredToMeanASizeTwiceIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWith(LIST_IS_EMPTY, ValueName.Stdlib.operation("List", "length")));

        assertTrue(e.getMessage().contains("List.isEmpty"), e.getMessage());
    }

    /** An operation the library does not declare is refused, as any fact about one is. */
    @Test
    void aSizeTheLibraryDoesNotDeclareIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> bindWith(LIST_IS_EMPTY, ValueName.Stdlib.operation("List", "girth")));
    }

    /** The binding, over the declarations the language has plus one written here. */
    private static void bindWith(ValueName check, ValueName size) {
        List<OperationFacts.Declared> gained = new ArrayList<>(OperationFacts.declarations());
        gained.add(new OperationFacts.Declared(check,
                new OperationFact.MeansTheSameAsASizeOfNought(size)));
        OperationFactBinder.bindAll(DefaultStdlib.get(), gained);
    }
}
