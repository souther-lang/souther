package souther.compiler.jvm;

import org.junit.jupiter.api.Test;
import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every declaration the language gives has a class on this backend.
 *
 * <p>Such a declaration belongs to no module of a compilation, so nothing generates it: what stands
 * behind it is a class souther-runtime ships by hand. One the runtime does not ship is a name that
 * types and evaluates and has nothing behind it, which is a fault in this compiler and shows up as
 * a linkage error in whatever model happens to write it.
 *
 * <p>This used to be settled where the library was loaded, as a registration the loader refused
 * against. It is asked here instead, because which declarations are provided rather than generated
 * is this backend's answer and not the library's — another backend may generate the same
 * declaration and be no less right (ADR-0087, amended by #1010). The refusal is as loud either way:
 * both fail the build.
 */
class EveryLanguageDeclarationHasAJvmImplementationTest {

    @Test
    void theRuntimeShipsAClassForEachOfThem() {
        Map<String, Hir.Def> declared = DefaultStdlib.get().languageDeclarations();

        assertTrue(declared.containsKey("RoundingMode"),
                () -> "the language declares RoundingMode; this found " + declared.keySet());
        assertEquals(List.of(), declared.keySet().stream().sorted()
                        .filter(name -> !shipped(declared).contains(name)).toList(),
                "a declaration the language gives and this backend does not ship is one nothing"
                        + " emits classes for");
    }

    /** What souther-runtime ships, by the bare name the library declares it under: each registered
     *  sum, and the cases it is written in. A case is a declaration of its own and has a class of
     *  its own; registering the sum is what says the whole of it is provided. */
    private static Set<String> shipped(Map<String, Hir.Def> declared) {
        Set<String> names = new LinkedHashSet<>();
        for (String sum : SoutherJvmAbi.providedByTheRuntime()) {
            names.add(sum);
            if (declared.get(sum) instanceof Hir.SumData data) {
                for (Hir.Name one : data.cases()) {
                    if (one.answered() instanceof Hir.Name.Denoting named) {
                        names.add(named.type().name());
                    }
                }
            }
        }
        return names;
    }

    /** And the mapping is the ABI's, so a name that is nobody's declaration is refused rather than
     *  spelled. */
    @Test
    void andNothingElseIsSpelledAsOne() {
        assertEquals("souther.runtime.RoundingMode",
                SoutherJvmAbi.nameOfLanguageDeclaration(TypeSymbol.runtime("RoundingMode"))
                        .binaryName());
        assertThrows(IllegalStateException.class,
                () -> SoutherJvmAbi.nameOfLanguageDeclaration(TypeSymbol.primitive("Int")),
                "a primitive is not a declaration the language gives under this namespace");
    }
}
