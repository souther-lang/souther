package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Resolve;
import souther.compiler.check.SyntaxSymbols;
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
 * {@code Hir.Apply.written()} — and was broken all the same. A sentence is kept by whoever reads it;
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
                    || Hir.Def.class.isAssignableFrom(m.getReturnType());
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
        for (Method m : Hir.Def.class.getMethods()) {
            if (m.getReturnType() == TypeName.class
                    && List.of(m.getParameterTypes()).contains(String.class)) {
                answering.add(m.getName());
            }
        }
        assertEquals(List.of(), answering,
                "a declaration says what it declares and is told nothing to say it with");
    }

    /**
     * And nothing public turns a key into one either.
     *
     * <p>A {@link souther.compiler.types.TypeKey} is what a class file carries, so it is structural
     * and public on purpose. What must not follow is a way to hand one back and be given the
     * identity the compiler reasons with, or the declaration it names: a key read off a class is
     * exactly what a reader would otherwise assemble, and the whole of the difference is that
     * nothing accepts it.
     */
    @Test
    void nothingPublicTurnsAKeyIntoAnIdentityOrADeclaration() {
        List<String> accepting = new ArrayList<>();
        for (Class<?> c : List.of(TypeName.class, souther.compiler.check.Declarations.class,
                souther.compiler.check.TypeScope.class, souther.compiler.check.Registry.class,
                Symbols.class, Hir.Def.class)) {
            for (Method m : c.getMethods()) {
                if (List.of(m.getParameterTypes()).contains(souther.compiler.types.TypeKey.class)) {
                    accepting.add(c.getSimpleName() + "." + m.getName());
                }
            }
            for (java.lang.reflect.Constructor<?> k : c.getConstructors()) {
                if (List.of(k.getParameterTypes()).contains(souther.compiler.types.TypeKey.class)) {
                    accepting.add("new " + c.getSimpleName());
                }
            }
        }
        assertEquals(List.of(), accepting,
                "a key is written down and read back; nothing here takes one");
    }

    /** A declaration says which one it is without being told the module. */
    @Test
    void aDeclarationSaysItsKey() {
        assertEquals(new souther.compiler.types.TypeKey("lib", "Amount"),
                declarationOf(LIB, "Amount").declaredKey());
        assertNotEquals(declarationOf(APP_WITH_AMOUNT, "Amount").declaredKey(),
                declarationOf(LIB, "Amount").declaredKey());
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

    private static Hir.Module resolved(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        return Resolve.module(parsed, SyntaxSymbols.of(parsed));
    }

    private static Hir.Def declarationOf(String source, String name) {
        for (Hir.Def def : resolved(source).defs()) {
            if (def.name().equals(name)) {
                return def;
            }
        }
        throw new IllegalStateException("the fixture declares `" + name + "`");
    }
}
