package souther.compiler.jvm;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every declaration the language gives has a class on this backend, and this backend says which.
 *
 * <p>Such a declaration belongs to no module of a compilation, so nothing generates it: what stands
 * behind it is a class souther-runtime ships by hand. One the runtime does not ship is a name that
 * types and evaluates and has nothing behind it, which is a fault in this compiler and shows up as
 * a linkage error in whatever model happens to write it.
 *
 * <p>Which declarations those are is this backend's answer and not the library's — another backend
 * may generate the same declaration and be no less right (ADR-0087, amended by #1010).
 */
class EveryLanguageDeclarationHasAJvmImplementationTest {

    @Test
    void theRuntimeShipsAClassForEachOfThem() {
        List<TypeKey> declared = DefaultStdlib.get().languageDeclarationsIn("souther.decimal")
                .values().stream().map(def -> def.declares().key()).sorted().toList();

        assertTrue(declared.contains(new TypeKey("souther.decimal", "RoundingMode")),
                () -> "souther.decimal declares RoundingMode; this found " + declared);
        assertEquals(List.of(),
                declared.stream().filter(at -> !SoutherJvmAbi.providedByTheRuntime().contains(at))
                        .toList(),
                "a declaration the language gives and this backend does not ship is one nothing"
                        + " emits classes for");
    }

    /**
     * And the two names are not the same name, which is the whole of what this backend is saying.
     *
     * <p>{@code souther.decimal} declares it; {@code souther.runtime} is the package the class is
     * shipped in. A backend that generated the declaration instead would answer differently here
     * and nowhere else.
     */
    @Test
    void whatDeclaresItAndWhatItIsCalledAreTwoNames() {
        TypeSymbol roundingMode =
                TypeSymbols.declared(new TypeKey("souther.decimal", "RoundingMode"));

        assertEquals("souther.runtime.RoundingMode",
                SoutherJvmAbi.nameOfLanguageDeclaration(roundingMode).binaryName());
        assertEquals("souther.runtime.HALF_UP",
                SoutherJvmAbi.nameOfLanguageDeclaration(
                        TypeSymbols.declared(new TypeKey("souther.decimal", "HALF_UP")))
                        .binaryName());
    }

    /** And the mapping is read backwards from the same table, so a class name written out and read
     *  back comes to the declaration it was written for. */
    @Test
    void theClassNameReadsBackAsTheDeclarationItWasWrittenFor() {
        assertEquals(new TypeKey("souther.decimal", "RoundingMode"),
                SoutherJvmAbi.valueTypeCandidate("souther.runtime.RoundingMode"));
        assertEquals(new TypeKey("demo", "Quote"),
                SoutherJvmAbi.valueTypeCandidate("demo.Quote"),
                "every other value class is its type's own address");
    }

    /** A name that is nobody's declaration is refused rather than spelled. */
    @Test
    void andNothingElseIsSpelledAsOne() {
        assertThrows(IllegalStateException.class,
                () -> SoutherJvmAbi.nameOfLanguageDeclaration(TypeSymbol.primitive("Int")),
                "a primitive is not a declaration this backend ships a class for");
        assertThrows(IllegalStateException.class,
                () -> SoutherJvmAbi.nameOfLanguageDeclaration(
                        TypeSymbols.declared(new TypeKey("demo", "Quote"))),
                "a module's own declaration is generated, not shipped");
    }
}
