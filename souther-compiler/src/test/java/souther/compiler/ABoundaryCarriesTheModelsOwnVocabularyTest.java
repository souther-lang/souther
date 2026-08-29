package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The language declares vocabulary of its own — what a division by zero answers with, what a rounding
 * takes, the reserved `Raw` — and each says what one of its operations can answer or take. A named
 * type that crosses is one a model declares (spec {@code [#a-boundary-carries-the-models-own-vocabulary]}),
 * so none of those may stand where an external representation crosses. Before this they were written
 * freely: a parameter compiled and failed at run with a reflection exception, and an output union
 * raised inside codegen.
 *
 * <p>A behavior's boundary is not the only place something crosses. A data field crosses too, at any
 * depth, and so does the base a newtype is written from (spec {@code [#collections]}); those were
 * asked by nobody, or answered by whether a decoder node happened to be on the declaration, which is
 * a fact about the compiler rather than about the model.
 */
class ABoundaryCarriesTheModelsOwnVocabularyTest {

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    private static void refuses(String signature, String body, String named) {
        refusesModel("module demo\n\n" + signature + "\n" + body + "\n", named);
    }

    /** The same rule, where what crosses is written as a declaration rather than as a signature. */
    private static void refusesDeclaring(String declaration, String named) {
        refusesModel("module demo\n\n" + declaration + "\n", named);
    }

    private static void refusesModel(String model, String named) {
        CompileException e = err(model);
        assertTrue(e.getMessage().contains("E1325"), e.getMessage());
        assertTrue(e.getMessage().contains("`" + named + "`"), "names the type: " + e.getMessage());
        assertTrue(e.getMessage().contains("Declare this as a type of the model"),
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
    void aUnionMemberSpelledLikeAPrimitiveIsHeldToTheScalarRule() {
        // The one position a name may be a scalar's. `Int | DivisionByZero` is a primitive beside a
        // case, so a member is asked which of the two it is; `Raw` is spelled like a primitive and
        // stands for no scalar, which is the language's word rather than a model's either way.
        refuses("behavior f : (n: Int) -> Int | Raw", "let f (n) = n", "Raw");
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

    @Test
    void aFieldTakesATypeTheLanguageDeclares() {
        refusesDeclaring("data X = { e: DivisionByZero }", "DivisionByZero");
    }

    @Test
    void aFieldCarryingOneInACollectionIsAskedAtItsDepth() {
        // spec [#collections] says a data field crosses at any depth, so every nominal position of
        // the walk is asked and not only the one the field type names.
        refusesDeclaring("data X = { ms: List<RoundingMode> }", "RoundingMode");
    }

    @Test
    void aFieldsMapValueIsAskedAtItsDepthToo() {
        // The other recursion arm. A key position has a rule of its own, so a fix that only reached
        // one would leave the quantifier — the field itself, or anywhere below it — unfixed and this
        // test is what tells the two apart.
        refusesDeclaring("data X = { m: Map<String, RoundingMode> }", "RoundingMode");
    }

    @Test
    void aFieldsMapKeyIsAskedToo() {
        // `RoundingMode` classifies as a key — it is an enumeration — so having a representation is
        // not what admits it. It is refused for whose vocabulary it is, as it is in a signature.
        refusesDeclaring("data X = { m: Map<RoundingMode, Int> }", "RoundingMode");
    }

    @Test
    void theBaseANewtypeIsWrittenFromIsAskedToo() {
        // a newtype delegates the whole input to its base's decoder, so the base is what crosses
        refusesDeclaring("data Wrapped = RoundingMode", "RoundingMode");
    }

    @Test
    void theReservedTypeIsAskedInAFieldToo() {
        refusesDeclaring("data X = { r: Raw }", "Raw");
    }

    @Test
    void aModelsOwnUnitDataStandsInAField() throws Exception {
        // The other side of the same rule: a unit data is the model's own vocabulary, so it crosses.
        // Held by taking one across rather than by compiling: what admitting it is worth is that the
        // value goes out and comes back, through the codec a unit's class is generated with. That no
        // decoder node sits on the declaration is a fact about the compiler's representation, which
        // is what the refusal used to read.
        assertEquals("{\"u\":{}}", Crossing.of("""
                module demo

                data Undivided

                data X = { u: Undivided }

                behavior echo : (x: X) -> X
                let echo (x) = x
                """, "demo", "echo", "{\"u\":{}}"));
    }
}
