package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A published module read back means what it meant where it was written, and says so in the terms
 * the compiler settles rather than in the words the author spelled.
 *
 * <p>What a comparison of two builds needs is exactly that. Whether two declarations say the same
 * thing is a question about what they mean; asked of their text it becomes a question about how they
 * were written, and every way of writing one thing differently has to be answered again by whoever
 * is asking. Here nothing is answered again: the front end reads the module and what comes back
 * carries which declaration each name reaches.
 */
class APublishedModuleIsReadAsTheCompilerReadsItTest {

    /** It writes `length` bare, which is what its import is for. */
    private static final String LIB = """
            module lib.text exposing ( Title )
            import String ( length )

            data Title = String
                invariant length(value) > 0
            """;

    /** And this one names that type without importing it, which the language allows. */
    private static final String QUALIFYING = """
            module app.uses

            data Note = { title: lib.text.Title }
            """;

    /** A bare name an import brought in is read as what it stands for. */
    @Test
    void aBareNameAnImportBroughtInIsReadAsWhatItStandsFor() {
        Hir.Module read = universeOf(LIB).resolved("lib.text");

        assertNotNull(read, "the module is published and this compiler reads it");
        ValueName calls = calledByTheInvariantOf(read, "Title");
        assertInstanceOf(ValueName.Stdlib.class, calls,
                "`length` was brought in by an import and stands for a standard-library function");
        assertEquals("String", ((ValueName.Stdlib) calls).alias());
        assertEquals("length", ((ValueName.Stdlib) calls).name());
    }

    /**
     * A module named with a qualifier and never imported is read too.
     *
     * <p>A type is reachable qualified whether or not it was imported, so the modules a set of
     * declarations reaches are not the modules its import lines name.
     */
    @Test
    void aModuleReachedWithoutAnImportIsRead() {
        Map<String, byte[]> both = Compiler.compileModules(List.of(LIB, QUALIFYING));
        PublishedUniverse universe = PublishedUniverse.of(new ClassFileDeclarations(both::get));

        Hir.Module uses = universe.resolved("app.uses");

        assertNotNull(uses);
        assertNotNull(universe.resolved("lib.text"),
                "the module its field's type is declared by was read, with nothing importing it");
    }

    /** Reading one twice answers with the one reading. */
    @Test
    void aModuleIsReadOnce() {
        PublishedUniverse universe = universeOf(LIB);

        assertSame(universe.resolved("lib.text"), universe.resolved("lib.text"));
    }

    /** Classes that declare nothing of that name answer with nothing. */
    @Test
    void whatIsNotPublishedIsNotRead() {
        PublishedUniverse universe = universeOf(LIB);

        assertNull(universe.resolved("nothing.here"));
        org.junit.jupiter.api.Assertions.assertFalse(universe.declares("nothing.here"));
    }

    /** What the invariant of {@code type} calls, as the front end answered it. */
    private static ValueName calledByTheInvariantOf(Hir.Module module, String type) {
        for (Hir.Def def : module.defs()) {
            if (def instanceof Hir.Data data && data.name().equals(type)) {
                Hir.Expr clause = data.invariants().get(0).expr();
                Hir.Apply call = (Hir.Apply) ((Hir.Binary) clause).left();
                return ((Hir.Var.Denoting) call.function()).denotes();
            }
        }
        throw new IllegalStateException("no `" + type + "` in " + module.name());
    }

    private static PublishedUniverse universeOf(String source) {
        Map<String, byte[]> classes = Compiler.compile(source);
        return PublishedUniverse.of(new ClassFileDeclarations(classes::get));
    }
}
