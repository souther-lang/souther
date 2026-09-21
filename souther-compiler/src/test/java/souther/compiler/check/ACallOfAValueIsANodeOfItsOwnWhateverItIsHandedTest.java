package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A build the emitted tree makes by calling the method its value is emitted as is a node of its own,
 * whether the method takes nothing or takes the values its root region demands.
 *
 * <p>Where it was a {@link Hir.Materialised} whose body happened to be a reference to the value or
 * an application of one, a reader had to test that shape to know it held a call and not a body.
 */
class ACallOfAValueIsANodeOfItsOwnWhateverItIsHandedTest {

    private static final String SOURCE = """
            module m exposing (f)

            let base = List.length([1, 2, 3])
            let left = base + 1
            let right = base + 2
            let both = left + right

            behavior f : (n: Int) -> Int
            let f (n) = both
            """;

    private static Hir.Expr lowered(String name) {
        return Compiler.compiled(SOURCE, "m").db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName(name)))
                .value().value().writtenBody();
    }

    private static void collect(Hir.Expr e, List<Hir.Expr> out) {
        if (e == null) {
            return;
        }
        out.add(e);
        Hir.forEachChild(e, child -> collect(child, out));
    }

    private static List<Hir.Expr> nodes(Hir.Expr e) {
        List<Hir.Expr> out = new ArrayList<>();
        collect(e, out);
        return out;
    }

    @Test
    void aMethodThatTakesNothingAndOneThatTakesValuesAreTheSameKindOfNode() {
        List<Hir.ValueInvocation> calls = nodes(lowered("f")).stream()
                .filter(Hir.ValueInvocation.class::isInstance)
                .map(Hir.ValueInvocation.class::cast).toList();

        assertTrue(calls.stream().anyMatch(call -> call.arguments().isEmpty()),
                "a value that names no other value is called with nothing");
        assertTrue(calls.stream().anyMatch(call -> !call.arguments().isEmpty()),
                "a value that names others is called with the bindings that hold them");
    }

    @Test
    void aValueAnotherModuleDeclaresIsCalledAsTheSameKindOfNode() {
        Compilation compiled = Compiler.compiledModules(List.of("""
                module up exposing (cap)

                let cap = List.length([1, 2, 3])
                """, """
                module down exposing (f)

                import up ( cap )

                behavior f : (x: Int) -> Int
                let f (x) = cap
                """), ModulePath.EMPTY, new ArrayList<>());
        Hir.Expr body = compiled.db()
                .ask(new Bodies.LoweredBody("down", new DefinitionName("f")))
                .value().value().writtenBody();

        List<Hir.Expr> all = nodes(body);
        assertTrue(all.stream().anyMatch(each -> each instanceof Hir.ValueInvocation call
                        && call.arguments().isEmpty() && call.value().toString().endsWith("cap")),
                "a value another module runs is called, and takes nothing here");
        assertFalse(all.stream().anyMatch(each -> each instanceof Hir.Materialised build
                        && build.body() instanceof Hir.Var.Denoting named
                        && named.denotes().equals(build.value())),
                "a build that carries a body is not a reference to the value it is of");
    }

    @Test
    void aBuildThatCarriesABodyHoldsNoCallOfItsOwnValue() {
        for (Hir.Expr each : nodes(lowered("f"))) {
            if (each instanceof Hir.Materialised build) {
                Hir.Expr called = build.body() instanceof Hir.Apply call
                        ? call.function() : build.body();
                assertFalse(called instanceof Hir.Var.Denoting named
                                && named.denotes().equals(build.value()),
                        "a build that carries its body is not a call of the value it is of: "
                                + build.value());
            }
        }
    }
}
