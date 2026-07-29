package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * `Option<T>` is the name of the type a `?` field has, and a model may write it wherever it reads one
 * (issue #202). What it may not do is make one — that is the `?` field being given its value, and
 * nothing else — or answer one out of a behavior, which is a domain sum's job (ADR-0011).
 */
class OptionAsAWrittenTypeTest {

    private static final String HEAD = """
            module demo

            data Amount = Int
            data Receipt = { total: Amount }
            """;

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    // --- reading an optional: the type may be written -------------------------------------------

    @Test
    void aDataFieldMayNameTheType() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                data Note = { text: Option<String> }
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt
                let bill (a) = Receipt { total = a }
                """));
    }

    @Test
    void aBehaviorInputMayNameTheType() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                behavior bill : (o: Option<Int>) -> Receipt
                    constructs Receipt, Amount
                let bill (o) = Receipt { total = Amount(Option.withDefault(0, o)) }
                """));
    }

    @Test
    void aHelperMayNameTheTypeItReadsAndPassesOn() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                let firstOf (xs: List<Int>) : Option<Int> = List.get(0, xs)
                let orZero (o: Option<Int>) : Int = Option.withDefault(0, o)
                let bill (a) = Receipt { total = Amount(orZero(firstOf([ 1 ]))) }
                """));
    }

    @Test
    void aRecursiveHelperMayDeclareAnOptionalReturn() {
        // A recursive helper must declare its return type (spec 13.1), so naming the type is the only
        // way to write this one at all. It answers the absence it read — the binding that holds it —
        // rather than making one.
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                partial let firstOver (n: Int, xs: List<Int>) : Option<Int> = {
                    let head = List.get(0, xs)
                    match head with
                        | Some v -> if v > n then head else firstOver(n, List.drop(1, xs))
                        | None -> head
                }
                let bill (a) = Receipt { total = Amount(Option.withDefault(0, firstOver(1, [ 1, 2 ]))) }
                """));
    }

    @Test
    void aHelperMayNotAnswerAnAbsenceItDidNotRead() {
        // The same helper writing `None` in the arm rather than passing on what it read. This was
        // accepted before, and only in that position: the same helper inlined as a `List.filterMap`
        // step was refused, so one helper had two answers depending on where it was used.
        CompileException e = err(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                partial let firstOver (n: Int, xs: List<Int>) : Option<Int> =
                    match List.get(0, xs) with
                        | Some v -> if v > n then List.get(0, xs) else firstOver(n, List.drop(1, xs))
                        | None -> None
                let bill (a) = Receipt { total = Amount(Option.withDefault(0, firstOver(1, [ 1, 2 ]))) }
                """);
        assertTrue(e.getMessage().contains("E1303"), e.getMessage());
    }

    @Test
    void aFilterMapStepMayNotDropEverything() {
        // ADR-0011's reason for the rule: absence the model owns is a case of its own sum, and a step
        // for `List.filterMap` has to answer an optional it read (issue #166).
        CompileException e = err(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                let drop (n: Int) : Option<Int> = match List.get(0, [ n ]) with
                    | Some v -> None
                    | None -> None
                let bill (a) = Receipt { total = Amount(List.length(List.filterMap(drop, [ 1, 2 ]))) }
                """);
        assertTrue(e.getMessage().contains("E1303"), e.getMessage());
    }

    @Test
    void aFunctionTypeMayNameTheTypeItsResultIs() {
        // A function-typed parameter must be annotated (spec 13.1), so a combinator taking a step that
        // answers an optional needs the name too.
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                let keep (n: Int) : Option<Int> = List.get(0, [ n ])
                let firstKept (step: (Int) -> Option<Int>, xs: List<Int>) : Int =
                    Option.withDefault(0, List.get(0, List.filterMap(step, xs)))
                let bill (a) = Receipt { total = Amount(firstKept(keep, [ 1, 2 ])) }
                """));
    }

    @Test
    void aLocalBindingMayNameTheTypeItReads() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                let bill (a) = {
                    let p: Option<Int> = List.get(0, [ 1 ])
                    Receipt { total = Amount(Option.withDefault(0, p)) }
                }
                """));
    }

    // --- making an optional: the `?` field, and nowhere else -------------------------------------

    @Test
    void aFieldIsStillWhereAnOptionalIsMade() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                data Note = { text: String? }
                behavior write : (a: Amount) -> Note
                    constructs Note
                let write (a) = Note { text = None }
                """));
    }

    @Test
    void aFieldTakesAnOptionalMadeByARule() {
        // The permission reaches the branches of the value being given to the field (ADR-0011).
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                data Note = { text: String? }
                behavior write : (a: Amount) -> Note
                    constructs Note
                let write (a) = Note { text = if a.value > 0 then "positive" else None }
                """));
    }

    @Test
    void anAnnotationDoesNotLicenseMakingOne() {
        CompileException e = err(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                let bill (a) = {
                    let p: Option<Int> = None
                    Receipt { total = Amount(Option.withDefault(9, p)) }
                }
                """);
        assertTrue(e.getMessage().contains("E1303"), e.getMessage());
    }

    @Test
    void aHelperMayNotFabricateAnAbsence() {
        CompileException e = err(HEAD + """
                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt, Amount
                let nothing (n: Int) : Option<Int> = None
                let bill (a) = Receipt { total = Amount(Option.withDefault(7, nothing(1))) }
                """);
        assertTrue(e.getMessage().contains("E1303"), e.getMessage());
    }

    // --- answering one out of a behavior --------------------------------------------------------

    @Test
    void aBehaviorMayNotOutputAnOptional() {
        CompileException e = err(HEAD + """
                behavior bill : (a: Amount) -> Option<Int>
                let bill (a) = List.get(0, [ 1 ])
                """);
        assertTrue(e.getMessage().contains("outputs an optional"), e.getMessage());
        assertTrue(e.getMessage().contains("|"), "the message points at the domain sum: " + e.getMessage());
    }

    @Test
    void aCompositionIsNoLongerBlamedForAnOptionalOutput() {
        // Before, the pair was reported as unable to compose (E1701), which is accurate and unhelpful:
        // what the author wrote is an output the language refuses.
        CompileException e = err(HEAD + """
                behavior first : (a: Amount) -> Option<Int>
                let first (a) = List.get(0, [ 1 ])
                behavior second : (n: Int) -> Receipt
                    constructs Receipt, Amount
                let second (n) = Receipt { total = Amount(n) }
                behavior both = first >-> second
                """);
        assertTrue(e.getMessage().contains("outputs an optional"), e.getMessage());
    }

    @Test
    void aBehaviorMayStillOutputADataWithAnOptionalField() {
        assertDoesNotThrow(() -> Compiler.compile(HEAD + """
                data Note = { text: String? }
                behavior write : (a: Amount) -> Note
                    constructs Note
                let write (a) = Note { text = None }
                """));
    }
}
