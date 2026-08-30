package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Severity;
import souther.compiler.diag.DiagnosticCode;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row may name as a case, and what a row that was never read reports.
 *
 * <p>Two facts about the language that something else is written against, and neither is safe to
 * carry as a sentence. A row states a case by naming it, and whether an answer is that case is read
 * off the answer — so the names a row can write have to be names an answer can be read as, or the
 * reading would have to grow a way of recognising something no answer says of itself.
 *
 * <p>Held here rather than argued about. If either stops being true, whoever changed it is told by
 * this rather than by an output reporting that a row it was handed does not hold.
 */
class WhatARowMayNameAsACaseIsWhatAValueCanBeReadAsTest {

    /**
     * A primitive standing as a case of a union is not a name a row can write.
     *
     * <p>What a row names as a case is resolved as a value, and a primitive is not one — so
     * {@code -> Int} is refused where it is written and no row states such a case. What reads an
     * answer's case is the declaration the value is of, which is what every case a row can name has
     * and a primitive has not. The two go together: a row that could name it would be a row nothing
     * could be read against.
     */
    @Test
    void aPrimitiveStandingAsACaseIsNotANameARowCanWrite() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data DivisionByZero = { why: String }

                behavior divide : (a: Int, b: Int) -> Int | DivisionByZero
                    constructs DivisionByZero

                let divide (a, b) =
                    if b == 0 then DivisionByZero { why = "zero" } else a / b

                example divide
                    | "the whole case" : (6, 3) -> Int
                """));

        assertTrue(refused.getMessage().contains("E1023"),
                () -> "a row naming a primitive as a case is refused: " + refused.getMessage());
    }

    /** And the same answer written as a value is a row like any other, so the refusal above is
     *  about naming a case and not about the type. */
    @Test
    void andThatAnswerWrittenAsAValueIsARowLikeAnyOther() {
        Compiler.compile("""
                module demo

                data DivisionByZero = { why: String }

                behavior divide : (a: Int, b: Int) -> Int | DivisionByZero
                    constructs DivisionByZero

                let divide (a, b) =
                    if b == 0 then DivisionByZero { why = "zero" } else a / b

                example divide
                    | "a good one" : (6, 2) -> 3
                    | "the other" : (1, 0) -> DivisionByZero
                """);
    }

    /**
     * A row whose evaluation stopped before its values is a row the language refuses the program
     * for.
     *
     * <p>What such a row states is nothing, and it says so carrying no reason: there is an
     * evaluation of it and how far it got is what that says. Which is only worth saying while every
     * way of stopping there is a way the program is refused — a warning among them would put a row
     * with no values into a program an output is handed, beside no reason for having none.
     *
     * <p>Not every row an output is handed with no values: a reading can never reach a row at all,
     * which the language accepts, and such a row crosses saying why nothing read it. What is
     * checked here is the other kind, and each code is one of its ways — a row that hands over
     * another number of inputs or whose fixture would not build (E1903), one naming a case the
     * behavior cannot answer with (E1904), one that spent its budget (E1910), one that did not
     * answer within its wait (E1923), and one whose stack ran out (E1924).
     */
    @Test
    void aRowThatStoppedBeforeItsValuesIsOneTheLanguageRefusesTheProgramFor() {
        for (DiagnosticCode code : new DiagnosticCode[] {DiagnosticCode.E1903,
                DiagnosticCode.E1904, DiagnosticCode.E1910, DiagnosticCode.E1923,
                DiagnosticCode.E1924}) {
            assertEquals(Severity.ERROR, code.severity(),
                    () -> code + " stops a row before its values, so a program carrying one is"
                            + " refused");
        }
    }
}
