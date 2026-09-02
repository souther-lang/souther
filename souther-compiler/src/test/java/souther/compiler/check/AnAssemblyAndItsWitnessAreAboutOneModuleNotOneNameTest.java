package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A module's assembly and the witness that every declaration in it came out have to be about the
 * same module, and a name does not say they are.
 *
 * <p>{@link Prepared} answers for a module out of two values: what a check reads comes from the
 * assembly, and what may only be read where the module is whole rests on the witness. Held together
 * by name alone, two compilations that each write a {@code module m} pair — the fields of one
 * module's declarations beside the claim made about another's. Every reader below is then told
 * something true of a module it is not looking at.
 *
 * <p>What the two have in common when they belong together is the settled module they were both
 * built from, and that is what is compared. Two modules of one name are two trees.
 */
class AnAssemblyAndItsWitnessAreAboutOneModuleNotOneNameTest {

    private static final String ONE = """
            module m exposing ( T )

            data T = { a: Int }
            """;

    /** The same name over a declaration that says something else, so that a pairing of the two is a
     *  pairing a name cannot tell apart. */
    private static final String OTHER = """
            module m exposing ( T )

            data T = { b: Int }
            """;

    @Test
    void twoModulesOfOneNameDoNotPair() {
        Desugared.Module declarations = declarationsOf(ONE);
        CheckSurface assembly = assemblyOf(OTHER);

        assertEquals("m", declarations.name());
        assertEquals("m", assembly.name());

        assertThrows(IllegalArgumentException.class,
                () -> Prepared.prepare(declarations, assembly),
                "an assembly of one module was paired with the witness of another, and the two"
                        + " agreeing on a name is all it took");
    }

    /** And the pair that does belong together is made, so the refusal is about the pairing and not
     *  about the values being unreachable. */
    @Test
    void theTwoBuiltFromOneModuleDoPair() {
        assertNotNull(Prepared.prepare(declarationsOf(ONE), assemblyOf(ONE)));
    }

    private static Desugared.Module declarationsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        Desugared.Module module = compilation.db().ask(new Shapes.Desugared("m")).value();
        assertNotNull(module, "the source under test does not get as far as being desugared");
        return module;
    }

    private static CheckSurface assemblyOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        CheckSurface surface = compilation.db().ask(new Shapes.CheckSurface("m")).value();
        assertNotNull(surface, "the source under test does not get as far as being assembled");
        return surface;
    }
}
