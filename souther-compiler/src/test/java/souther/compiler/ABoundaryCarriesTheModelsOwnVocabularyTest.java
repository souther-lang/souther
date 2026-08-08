package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The language declares vocabulary of its own — what a division by zero answers with, what a rounding
 * takes, the reserved `Raw` — and each says what one of its operations can answer or take. A behavior
 * publishes what a model declared, so none of those may stand in its boundary. Before this they were
 * written freely: a parameter compiled and failed at run with a reflection exception, and an output
 * union raised inside codegen.
 */
class ABoundaryCarriesTheModelsOwnVocabularyTest {

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    private static void refuses(String signature, String body, String named) {
        CompileException e = err("module demo\n\n" + signature + "\n" + body + "\n");
        assertTrue(e.getMessage().contains("E1325"), e.getMessage());
        assertTrue(e.getMessage().contains("`" + named + "`"), "names the type: " + e.getMessage());
        assertTrue(e.getMessage().contains("declare this as a type of the model"),
                "says what to write: " + e.getMessage());
    }

    @Test
    void anOutputThatIsOneOnItsOwnIsAskedToo() {
        refuses("behavior f : (n: Int) -> DivisionByZero", "", "DivisionByZero");
    }

    @Test
    void anOutputCarryingOneInACollectionIsAskedToo() {
        refuses("behavior f : (n: Int) -> List<DivisionByZero>", "let f (n) = []", "DivisionByZero");
    }

    @Test
    void aParameterMayNotTakeATypeTheLanguageDeclares() {
        refuses("behavior f : (x: DivisionByZero) -> Int", "let f (x) = 1", "DivisionByZero");
    }

    @Test
    void anOutputUnionMemberIsAskedToo() {
        // Before, this reached the backend's question of how a member is discriminated, which had no
        // arm for a name no module declares and raised an `IllegalStateException`.
        refuses("behavior f : (n: Int) -> Int | DivisionByZero", "let f (n) = Int.divide(10, n)",
                "DivisionByZero");
    }

    @Test
    void theReservedTypeIsAskedLikeAnyOtherName() {
        // `Raw` is spelled like a primitive and is not one: no stage produces it, and the module that
        // compiled published `Behavior<souther.Raw, Long>` for a class that does not exist.
        refuses("behavior f : (x: Raw) -> Int", "let f (x) = 1", "Raw");
    }

    @Test
    void aParseFailureCaseIsAskedToo() {
        refuses("behavior f : (x: NotANumber) -> Int", "let f (x) = 1", "NotANumber");
    }

    @Test
    void aTypeTheLanguageDeclaresForItsOwnOperationIsAskedToo() {
        // `RoundingMode` is declared, and by the language: it says what `Decimal.round` takes.
        refuses("behavior f : (m: RoundingMode) -> Int", "let f (m) = 1", "RoundingMode");
    }

    @Test
    void aCollectionCarryingOneIsAskedAtItsDepth() {
        refuses("behavior f : (xs: List<DivisionByZero>) -> Int", "let f (xs) = List.length(xs)",
                "DivisionByZero");
    }

    @Test
    void aMapCarryingOneUnderItsValueIsAskedToo() {
        refuses("behavior f : (m: Map<String, NotANumber>) -> Int", "let f (m) = Map.size(m)",
                "NotANumber");
    }

    @Test
    void aModelsOwnCaseIsWhatTheBehaviorAnswers() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Undivided

                behavior divide : (a: Int, b: Int) -> Int | Undivided
                    constructs Undivided
                let divide (a, b) = {
                    guard b /= 0 else Undivided
                    a
                }
                """));
    }

    @Test
    void aModelMayStillReadTheLanguagesCaseInsideItsBody() {
        // The rule is about what crosses. Inside a body the language's own case is what `Int.divide`
        // answers, and a `match` arm names it as it always has.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Undivided

                behavior divide : (a: Int, b: Int) -> Int | Undivided
                    constructs Undivided
                let divide (a, b) = match Int.divide(a, b) with
                    | Int as n -> n
                    | DivisionByZero -> Undivided
                """));
    }

    @Test
    void aDataAModelDeclaredCrossesWhateverItHoldsInside() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Note = { text: String }

                behavior write : (n: Note) -> Note
                let write (n) = n
                """));
    }
}
