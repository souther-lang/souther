package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.CompleteSignature;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.SizeAgainstItsSource;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule names an argument of an operation, and what an operation's arguments are is the library's to
 * say. Where the two disagree there is nothing to be done at a call — the rule is about an argument
 * that is not there, or is not the kind of thing the rule is about — so the disagreement is said where
 * the tables are bound rather than met as a missing answer at whichever reader arrives first.
 *
 * <p>This holds the binding to saying it. Each rule below is one a reader would have had to defend
 * itself against, and each is now a build that does not start.
 */
class ARuleIsHeldToTheDeclarationItIsAboutTest {

    /** A row written here, including one naming an operation the library does not have — which is
     * what several of these are for, so it takes the spelling apart rather than asking the library. */
    private static ValueName op(String qualified) {
        int dot = qualified.lastIndexOf('.');
        return ValueName.Stdlib.operation(qualified.substring(0, dot), qualified.substring(dot + 1));
    }

    /** The operation read against the library, as the binder reads every one before holding a
     *  fact to it — so an operation the library does not have is refused here, one question before
     *  the argument. */
    private static CompleteSignature declared(String operation) {
        return OperationFactBinder.declaredSignature(DefaultStdlib.get(), op(operation));
    }

    private static void bindCarried(String operation, ArgumentRef container) {
        OperationFactBinder.holdToTheDeclaration(declared(operation), container,
                new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                "the container a predicate reads");
    }

    private static void bindBuilt(String operation, ArgumentRef from) {
        OperationFactBinder.holdToTheDeclaration(declared(operation),
                new BuiltFrom<>(new ElementLineage.SameAs<>(new ElementLineage.Source<>(from, 1)),
                        SizeAgainstItsSource.AT_MOST).from(),
                new ArgumentRef.TheContainer(), TypeRequirement.CONTAINER,
                "the container something is built from");
    }

    /**
     * A key decides how many {@code List.distinctBy} answers and never whether it answers any, and
     * it answers whichever value it projects rather than a truth — so no element is a witness of
     * its answer by its key holding, and a law saying so is refused where it meets the signature.
     * Read as one, a rule inside the key would be credited with deciding whether the answer is
     * empty, and a model nothing read would come back read.
     */
    @Test
    void aKeyIsNoWitness() {
        IllegalStateException key = assertThrows(IllegalStateException.class,
                () -> bindWitness("List.distinctBy", new SideAnswered(AnswerAspect.EMPTINESS, true),
                        new SideAnswered(AnswerAspect.TRUTH, true)));
        assertTrue(key.getMessage().contains("has no TRUTH"), key.getMessage());
    }

    /** A witness law, bound to the declaration it is about. */
    private static void bindWitness(String operation, SideAnswered result,
                                    SideAnswered ofTheClosure) {
        CompleteSignature declaration = declared(operation);
        OperationFactBinder.holdWitness(declaration, declaration.declaring(),
                new OperationFact.ResultHasAnElementWitness(result, ofTheClosure));
    }

    /** An operation walking no container with a closure has no element to witness anything. */
    @Test
    void aWitnessOfAnOperationThatWalksNothingIsRefused() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindWitness("List.reverse", new SideAnswered(AnswerAspect.EMPTINESS, true),
                        new SideAnswered(AnswerAspect.TRUTH, true)));
        assertTrue(e.getMessage().contains("hands no closure the elements of a container"),
                e.getMessage());
    }

    /**
     * A side the result does not have, or a side the closure's answer does not have, is a law about
     * something that is not there — read anyway, it would carry a statement back to one the model
     * never made.
     */
    @Test
    void aWitnessOnASideThatIsNotThereIsRefused() {
        IllegalStateException result = assertThrows(IllegalStateException.class,
                () -> bindWitness("List.filter", new SideAnswered(AnswerAspect.TRUTH, true),
                        new SideAnswered(AnswerAspect.TRUTH, true)));
        assertTrue(result.getMessage().contains("what List.filter answers is"),
                result.getMessage());

        IllegalStateException present = assertThrows(IllegalStateException.class,
                () -> bindWitness("List.filter", new SideAnswered(AnswerAspect.EMPTINESS, true),
                        new SideAnswered(AnswerAspect.PRESENCE, true)));
        assertTrue(present.getMessage().contains("has no PRESENCE"), present.getMessage());

        IllegalStateException truth = assertThrows(IllegalStateException.class,
                () -> bindWitness("List.filterMap", new SideAnswered(AnswerAspect.EMPTINESS, true),
                        new SideAnswered(AnswerAspect.TRUTH, true)));
        assertTrue(truth.getMessage().contains("has no TRUTH"), truth.getMessage());
    }

    /** And the laws the library states, which bind. */
    @Test
    void theWitnessesTheLibraryStatesBind() {
        assertDoesNotThrow(() -> bindWitness("List.filterMap",
                new SideAnswered(AnswerAspect.EMPTINESS, true),
                new SideAnswered(AnswerAspect.PRESENCE, true)));
        assertDoesNotThrow(() -> bindWitness("List.flatMap",
                new SideAnswered(AnswerAspect.EMPTINESS, true),
                new SideAnswered(AnswerAspect.EMPTINESS, true)));
        assertDoesNotThrow(() -> bindWitness("Map.filterEntries",
                new SideAnswered(AnswerAspect.EMPTINESS, true),
                new SideAnswered(AnswerAspect.TRUTH, true)));
        assertDoesNotThrow(() -> bindWitness("List.all",
                new SideAnswered(AnswerAspect.TRUTH, false),
                new SideAnswered(AnswerAspect.TRUTH, false)));
    }

    @Test
    void anArgumentTheDeclarationDoesNotHave() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("String.contains", new ArgumentRef.At(7)));
        assertTrue(e.getMessage().contains("String.contains takes 2 argument(s)"), e.getMessage());
    }

    @Test
    void anArgumentThatIsNotWhatTheRuleIsAbout() {
        // `String.contains(needle, haystack)` reads a string, and a shape says what became of a
        // container's elements — of a string this names only its length.
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("String.contains", new ArgumentRef.At(1)));
        assertTrue(e.getMessage().contains("is String, not a container"), e.getMessage());
        assertTrue(e.getMessage().contains("named as the container a predicate reads"),
                e.getMessage());
    }

    @Test
    void aPartOfSomethingTheSignatureSaysItDoesNotHand() {
        // `List.contains(value, xs)` applies no closure, so there is no container it hands one.
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("List.contains", new ArgumentRef.TheContainer()));
        assertTrue(e.getMessage().contains("hands one nothing a container holds"), e.getMessage());
    }

    @Test
    void anOperationTheLibraryDoesNotDeclare() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("List.containsTwice", new ArgumentRef.At(1)));
        assertTrue(e.getMessage().contains("which the library does not declare"), e.getMessage());
    }

    /**
     * A position written where the signature already answers is two answers to one question, and two
     * answers are what come apart later — which is what {@code List.all} had, its container written in
     * one table and derived in another.
     */
    @Test
    void aPositionTheSignatureAlreadyAnswers() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindBuilt("List.filter", new ArgumentRef.At(1)));
        assertTrue(e.getMessage().contains("writes the argument its signature already answers"),
                e.getMessage());
    }

    /** And the rules the library actually has: every row of every table, on the first ask. */
    @Test
    void theRulesTheCheckShipsWith() {
        assertDoesNotThrow(() -> {
            DischargeRules.builtOperations();
            DischargeRules.carryingOperations();
            DischargeRules.projections();
        });
    }

    /** The binding reads what the declaration says, so a rule it agrees with binds. */
    @Test
    void aRuleThatAgreesWithTheDeclaration() {
        assertDoesNotThrow(() -> OperationFactBinder.holdToTheDeclaration(declared("List.reverse"),
                new ArgumentRef.At(0), new ArgumentRef.TheContainer(),
                TypeRequirement.CONTAINER, "the container something is built from"));
    }
}
