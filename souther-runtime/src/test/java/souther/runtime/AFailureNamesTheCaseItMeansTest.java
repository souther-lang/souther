package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a violated {@code ensures} records, and what it means by it.
 *
 * <p>Held here rather than through a compile because what is at stake is what the value says, and
 * two modules each declaring a {@code Denied} is a pair a compile cannot put in one behavior's
 * output — a signature whose leaves go by one written name is refused where it is declared. The
 * value travels further than one behavior: into a log, into whatever reads a run's aborts, where
 * the two are met side by side.
 */
class AFailureNamesTheCaseItMeansTest {

    private static final DeclaredCase SALES_DENIED = new DeclaredCase("sales", "Denied");
    private static final DeclaredCase SECURITY_DENIED = new DeclaredCase("security", "Denied");

    /** A case is the module that declares it and the name written there. */
    @Test
    void twoModulesEachDeclaringOneNameAreTwoCases() {
        assertNotEquals(SALES_DENIED, SECURITY_DENIED);
        assertEquals("sales.Denied", SALES_DENIED.qualified());
    }

    /**
     * A rule written for one module's {@code Denied}, refusing another's, says both. What is left
     * out where the two coincide is a fact said twice — and whether they coincide is asked of the
     * cases. Asked of their names, this would drop the one thing the reader needed.
     */
    @Test
    void oneNameForTwoCasesIsNotOneFact() {
        assertEquals("ensures not held on shop.checkout: allowed, for Denied, answering Denied",
                new EnsuresFailure("shop", "checkout", "allowed",
                        SALES_DENIED, SECURITY_DENIED).toString());
    }

    /** The same case, said once. */
    @Test
    void oneCaseIsSaidOnce() {
        assertEquals("ensures not held on shop.checkout: allowed, answering Denied",
                new EnsuresFailure("shop", "checkout", "allowed",
                        SALES_DENIED, SALES_DENIED).toString());
    }

    /** A rule guarded by a case that answered a leaf of it: both, and the reader is told which is
     *  which. */
    @Test
    void anArmOverASumSaysWhatItWasWrittenForAndWhatAnswered() {
        assertEquals("ensures not held on example.todo.findTodo: positive, for Errors, "
                        + "answering NotFound",
                new EnsuresFailure("example.todo", "findTodo", "positive",
                        new DeclaredCase("example.todo", "Errors"),
                        new DeclaredCase("example.todo", "NotFound")).toString());
    }

    /** A rule guarded by no case: there is neither a case it was written for nor a case the answer
     *  was, and nothing is said about either. */
    @Test
    void aRuleGuardedByNoCaseSaysNeither() {
        assertEquals("ensures not held on example.todo.findTodo: asked",
                new EnsuresFailure("example.todo", "findTodo", "asked", null, null).toString());
    }

    /** An unnamed clause has nothing to tell it apart from the behavior's others by. */
    @Test
    void anUnnamedClauseIsNotNamed() {
        assertEquals("ensures not held on example.todo.findTodo: answering NotFound",
                new EnsuresFailure("example.todo", "findTodo", null,
                        new DeclaredCase("example.todo", "NotFound"),
                        new DeclaredCase("example.todo", "NotFound")).toString());
    }

    /**
     * Half of the pair is not a weaker statement but a meaningless one: a rule applied to an answer
     * because the answer was this case says nothing with one side missing, and a message built from
     * it would read as though it were saying something.
     */
    @Test
    void aCaseWithoutItsCounterpartIsRefused() {
        assertThrows(IllegalArgumentException.class, () ->
                new EnsuresFailure("shop", "checkout", "allowed", SALES_DENIED, null));
        assertThrows(IllegalArgumentException.class, () ->
                new EnsuresFailure("shop", "checkout", "allowed", null, SALES_DENIED));
    }
}
