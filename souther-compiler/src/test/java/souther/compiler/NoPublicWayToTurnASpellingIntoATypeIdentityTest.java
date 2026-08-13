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
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
     * The one entry that answers with an identity of this module holds what it is handed to being
     * one. Its name says the declaration is this module's, and a declaration is an argument like any
     * other, so a caller can hand over another module's — which is how a {@code constructs} entry
     * naming an imported type was answered about a class of the module that names it.
     *
     * <p>Held to the name being declared here, which is as far as this can be held: a declaration
     * another module wrote under a name this one also writes is not told apart from one of this
     * module's, because nothing a declaration carries says which module wrote it.
     */
    @Test
    void aDeclarationOfAnotherModuleIsNotOneOfThisModulesOwn() {
        Symbols app = symbolsOf(APP);
        Ast.Def foreign = declarationOf(LIB, "Amount");

        IllegalArgumentException refused =
                assertThrows(IllegalArgumentException.class, () -> app.own(foreign));
        assertTrue(refused.getMessage().contains("not declared in"), refused.getMessage());
    }

    /** And the same question about this module's own declaration is answered. */
    @Test
    void aDeclarationOfThisModuleIsAnsweredWithItsName() {
        assertEquals(new TypeName("app", "Note"),
                symbolsOf(APP).own(declarationOf(APP, "Note")));
    }

    private static Symbols symbolsOf(String source) {
        return Symbols.of(resolved(source));
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
