package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.check.DischargeRules.Built;
import souther.compiler.check.DischargeRules.Cardinality;
import souther.compiler.check.DischargeRules.Carried;
import souther.compiler.check.DischargeRules.Reads;
import souther.compiler.check.DischargeRules.Shape;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;
import java.util.function.Function;

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
        return new ValueName.Stdlib(qualified.substring(0, dot), qualified.substring(dot + 1));
    }

    private static void bindCarried(String operation, Reads container) {
        DischargeRules.bind(
                Map.of(op(operation), new Carried(container, Set.of(Shape.PERMUTES))),
                Carried::container, new Reads.TheContainer(), Question::holdsElements,
                "the container a predicate reads");
    }

    private static void bindBuilt(String operation, Reads from) {
        DischargeRules.bind(
                Map.of(op(operation), new Built(from, Shape.SUBSET, Cardinality.AT_MOST)),
                Built::from, new Reads.TheContainer(), Question::holdsElements,
                "the container something is built from");
    }

    @Test
    void anArgumentTheDeclarationDoesNotHave() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("String.contains", new Reads.At(7)));
        assertTrue(e.getMessage().contains("String.contains takes 2 argument(s)"), e.getMessage());
    }

    @Test
    void anArgumentThatIsNotWhatTheRuleIsAbout() {
        // `String.contains(needle, haystack)` reads a string, and a shape says what became of a
        // container's elements — of a string this names only its length.
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("String.contains", new Reads.At(1)));
        assertTrue(e.getMessage().contains("is not the container a predicate reads"), e.getMessage());
    }

    @Test
    void aPartOfSomethingTheSignatureSaysItDoesNotHand() {
        // `List.contains(value, xs)` applies no closure, so there is no container it hands one.
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("List.contains", new Reads.TheContainer()));
        assertTrue(e.getMessage().contains("hands one nothing a container holds"), e.getMessage());
    }

    @Test
    void anOperationTheLibraryDoesNotDeclare() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> bindCarried("List.containsTwice", new Reads.At(1)));
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
                () -> bindBuilt("List.filter", new Reads.At(1)));
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

    /** The binding reads what the declaration says, so a table it agrees with binds. */
    @Test
    void aRuleThatAgreesWithTheDeclaration() {
        assertDoesNotThrow(() -> DischargeRules.bind(
                Map.of(op("List.reverse"), new Reads.At(0)),
                Function.identity(), new Reads.TheContainer(),
                (Type t) -> Question.holdsElements(t), "the container something is built from"));
    }
}
