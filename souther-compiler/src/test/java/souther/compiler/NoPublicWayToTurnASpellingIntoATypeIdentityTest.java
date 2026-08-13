package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Resolve;
import souther.compiler.check.Symbols;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.TypeName;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A spelling means something in the module that wrote it, and only the pass that reads that module
 * turns one into the type it denotes. Everything after holds the type.
 *
 * <p>This is checked against the shape of the API rather than against an answer, because the rule was
 * already written down three times — on {@code Symbols}, on {@code Resolve}, on
 * {@code Ast.Apply.written()} — and was broken all the same. A sentence is kept by whoever reads it;
 * a signature is kept by everyone. What a reader outside can reach is the whole of what it can do
 * wrong, so that is what is measured here.
 */
class NoPublicWayToTurnASpellingIntoATypeIdentityTest {

    private static final String LIB = """
            module lib exposing ( Amount )

            data Amount = Int
            """;

    private static final String APP = """
            module app

            data Note = { text: String }
            """;

    private static final String APP_WITH_AMOUNT = """
            module app2

            data Amount = { yen: Int }
            """;

    /**
     * No public method takes a spelling and answers with an identity. A caller outside the pass has
     * a type or it has nothing, and the way to get one is to be handed it.
     */
    @Test
    void nothingPublicOnSymbolsTakesAStringAndAnswersWithADeclarationOrItsName() {
        List<String> answering = new ArrayList<>();
        for (Method m : Symbols.class.getDeclaredMethods()) {
            if (!Modifier.isPublic(m.getModifiers())) {
                continue;
            }
            boolean identity = m.getReturnType() == TypeName.class
                    || Ast.Def.class.isAssignableFrom(m.getReturnType());
            boolean fromASpelling = List.of(m.getParameterTypes()).contains(String.class);
            if (identity && fromASpelling) {
                answering.add(m.getName());
            }
        }
        assertEquals(List.of(), answering,
                "a spelling reaches a declaration only through the pass that resolves it");
    }

    /** And the same holds of a declaration, which is what answers with an identity now that
     * nothing pairs a name with a module of its own. */
    @Test
    void nothingPublicOnADeclarationTakesAStringAndAnswersWithAnIdentity() {
        List<String> answering = new ArrayList<>();
        for (Method m : Ast.Def.class.getMethods()) {
            if (m.getReturnType() == TypeName.class
                    && List.of(m.getParameterTypes()).contains(String.class)) {
                answering.add(m.getName());
            }
        }
        assertEquals(List.of(), answering,
                "a declaration says what it declares and is told nothing to say it with");
    }

    /** And the pass's own way in is not reachable from outside it. */
    @Test
    void resolutionIsNotPartOfTheSurface() {
        for (Method m : Symbols.class.getDeclaredMethods()) {
            if (m.getName().equals("resolve") || m.getName().equals("resolveCase")) {
                assertFalse(Modifier.isPublic(m.getModifiers()),
                        m.getName() + " is the pass's own reading and belongs to it");
            }
        }
    }

    /**
     * A declaration answers with the type it declares, and there is no module for a caller to
     * supply. What one is asked through — a scope, a registry, a check — has no say in the answer,
     * so handing one somewhere it did not come from cannot name a declaration of wherever it is
     * being read.
     */
    @Test
    void aDeclarationAnswersWithTheModuleThatWroteIt() {
        assertEquals(new TypeName("app", "Note"), declarationOf(APP, "Note").declares());
        assertEquals(new TypeName("lib", "Amount"), declarationOf(LIB, "Amount").declares());
    }

    /**
     * Two modules that write one spelling declare two types, and holding either says which. This is
     * what nothing could tell apart while the module came from the reader: a declaration under a
     * name the reading module also writes was answered about the reader's.
     */
    @Test
    void oneSpellingWrittenByTwoModulesIsTwoDeclarations() {
        TypeName mine = declarationOf(APP_WITH_AMOUNT, "Amount").declares();
        TypeName theirs = declarationOf(LIB, "Amount").declares();

        assertEquals("Amount", mine.name());
        assertEquals("Amount", theirs.name());
        assertNotEquals(mine, theirs);
    }

    private static Ast.Module resolved(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    private static Ast.Def declarationOf(String source, String name) {
        for (Ast.Def def : resolved(source).defs()) {
            if (def.name().equals(name)) {
                return def;
            }
        }
        throw new IllegalStateException("the fixture declares `" + name + "`");
    }
}
