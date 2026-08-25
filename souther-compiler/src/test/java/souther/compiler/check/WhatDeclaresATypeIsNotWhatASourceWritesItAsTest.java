package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code RoundingMode} is declared by {@code souther.decimal}, called
 * {@code souther.runtime.RoundingMode} on this backend, and written {@code RoundingMode} and
 * nothing else. Three answers, and none of them is read off either of the others.
 *
 * <p>That the third does not follow from the first is the point. A module of the compilation is
 * reached through its own name, so a type belonging to {@code souther.decimal} could be expected to
 * be written {@code Decimal.RoundingMode} — and it is not, because how a source may write a name is
 * the language's rule and not a consequence of which module declares it. What the library declares
 * is on the lowest rung of every module's scope and is written bare (spec §stdlib).
 */
class WhatDeclaresATypeIsNotWhatASourceWritesItAsTest {

    private static final TypeSymbol ROUNDING_MODE =
            TypeSymbols.declared(new TypeKey("souther.decimal", "RoundingMode"));

    /** Written bare, and the bare spelling reaches the declaration `souther.decimal` wrote. */
    @Test
    void theBareSpellingReachesWhatTheLibraryDeclares() {
        assertTrue(Compiler.compile("""
                module demo exposing ( half )
                let half: RoundingMode = HALF_UP
                """).containsKey(souther.compiler.Emitted.declarations("demo")));
    }

    /**
     * And the module that declares it is not a qualifier anybody names it by.
     *
     * <p>`Decimal` is a qualifier — `Decimal.round(...)` is how the library's functions are called —
     * so this is not a spelling nothing could resolve. It reaches the library's functions and not
     * its types, and that is a rule of the language rather than a gap.
     */
    @Test
    void theModuleThatDeclaresItIsNoQualifierForIt() {
        assertThrows(souther.compiler.diag.CompileException.class, () -> Compiler.compile("""
                module demo exposing ( half )
                let half: Decimal.RoundingMode = HALF_UP
                """), "`Decimal.RoundingMode` is not how the library's own type is written");

        assertThrows(souther.compiler.diag.CompileException.class, () -> Compiler.compile("""
                module demo exposing ( half )
                let half: souther.decimal.RoundingMode = HALF_UP
                """), "and neither is the module's own name");
    }

    /** What it is called on this backend is the ABI's answer, and it is not the address. */
    @Test
    void whatItIsCalledHereIsNotWhereItIsDeclared() {
        assertEquals("souther.runtime.RoundingMode",
                SoutherJvmAbi.nameOfLanguageDeclaration(ROUNDING_MODE).binaryName());
        assertEquals(new TypeKey("souther.decimal", "RoundingMode"),
                SoutherJvmAbi.valueTypeCandidate("souther.runtime.RoundingMode"),
                "and the class name reads back as the declaration, not as a module of that name");
    }
}
