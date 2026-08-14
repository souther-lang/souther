package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module in one of these states got there by having the thing the state says happen to it.
 *
 * <p>{@link Resolved}, {@link Expandable} and {@link InvariantSettled} are three claims about one
 * module, and they used to be one type: whichever question you asked, what came back said only that
 * resolution had been over the tree. A reader that wanted an expandable module and one that wanted a
 * settled one were handed the same value, and what told them apart was which query they happened to
 * ask.
 *
 * <p>So the propositions here are about the ways in. Each state is reached from the one below it by
 * a step that performs what the state claims — the cycle check, the settling — and there is no other
 * way to reach it. What that forbids is the shape this replaces: a carrier with an operation that
 * takes a payload and hands the claim back, which is a way to assert anything about anything.
 */
class AStateIsReachedOnlyThroughWhatEstablishesItTest {

    private static final List<Class<?>> STATES =
            List.of(Resolved.class, Expandable.class, InvariantSettled.class);

    private static Resolved resolved(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        return Resolve.resolving(parsed, SyntaxSymbols.of(parsed)).module();
    }

    private static String signature(Method m) {
        StringBuilder sb = new StringBuilder(m.getName()).append('(');
        for (int i = 0; i < m.getParameterTypes().length; i++) {
            sb.append(i == 0 ? "" : ", ").append(m.getParameterTypes()[i].getSimpleName());
        }
        return sb.append(')').toString();
    }

    /** Nothing outside the pass that establishes a state can put one together. */
    @Test
    void noStateHasAPublicConstructor() {
        for (Class<?> state : STATES) {
            assertEquals(0, state.getConstructors().length,
                    state.getSimpleName() + " is arrived at, not built");
        }
    }

    /**
     * The ways in, named. One that appears later is a way of reaching a state that someone was
     * given, and it fails here until it is either narrowed or written down as these are.
     */
    @Test
    void everyWayIntoAStateComesFromTheStateBelowIt() {
        assertEquals(Set.of(), waysInto(Resolved.class),
                "resolution mints it, and there is nothing public to mint it with");
        assertEquals(Set.of("check(Resolved, Map)"), waysInto(Expandable.class));
        assertEquals(Set.of("settle(Expandable, Symbols, Map)"), waysInto(InvariantSettled.class));
    }

    private static Set<String> waysInto(Class<?> state) {
        Set<String> ways = new LinkedHashSet<>();
        for (Class<?> declaring : STATES) {
            for (Method m : declaring.getMethods()) {
                if (Modifier.isStatic(m.getModifiers()) && m.getReturnType() == state) {
                    ways.add(signature(m));
                }
            }
        }
        return ways;
    }

    /**
     * No state takes a tree. Handed one, every way in would be somewhere to make its claim about
     * anything — which is what {@code ResolvedModule.with} was, and why the claim it carried was
     * carried by nobody.
     */
    @Test
    void noStateTakesATree() {
        for (Class<?> state : STATES) {
            for (Method m : state.getMethods()) {
                assertFalse(List.of(m.getParameterTypes()).contains(Hir.Module.class),
                        state.getSimpleName() + "." + signature(m) + " takes a tree");
            }
            for (Constructor<?> k : state.getDeclaredConstructors()) {
                assertTrue(Modifier.isPrivate(k.getModifiers())
                                || !List.of(k.getParameterTypes()).contains(Hir.Module.class)
                                || state == Resolved.class,
                        state.getSimpleName() + " is built from a tree by something outside it");
            }
        }
    }

    /** And none of them answers with its own state, which is the same operation written as a method
     * on the value it would re-assert about. */
    @Test
    void noStateAnswersWithItself() {
        for (Class<?> state : STATES) {
            for (Method m : state.getMethods()) {
                assertFalse(!Modifier.isStatic(m.getModifiers()) && m.getReturnType() == state,
                        state.getSimpleName() + "." + signature(m) + " hands the claim back");
            }
        }
    }

    /** The way to an expandable module is the cycle check, so a module with a value defined in terms
     * of itself has no way through — and one without it does. */
    @Test
    void thewayToAnExpandableModuleIsTheCycleCheck() {
        Resolved wellFounded = resolved("""
                module m exposing ( n )

                let n = 1
                """);
        assertEquals("m", Expandable.check(wellFounded, Map.of()).name());

        Resolved reachesItself = resolved("""
                module m exposing ( a )

                let a = b
                let b = a
                """);
        CompileException refused =
                assertThrows(CompileException.class, () -> Expandable.check(reachesItself, Map.of()));
        assertTrue(refused.getMessage().contains("a"), refused.getMessage());
    }

    /**
     * The way to a settled module is the settling, so a clause naming a helper is the rule that
     * helper writes afterwards and is a call to it before. A reader of the settled state is reading
     * what the clause says; a reader of the state below it would have had to expand the call to find
     * out.
     */
    @Test
    void theWayToASettledModuleIsTheSettling() {
        Resolved resolved = resolved("""
                module m exposing ( Amount )

                data Amount = Int
                    invariant positive(value)

                let positive (n: Int) : Bool = n > 0
                """);
        Expandable expandable = Expandable.check(resolved, Map.of());

        assertTrue(clauseOf(expandable.module().defs(), "Amount") instanceof Hir.Apply,
                "the clause is a call to the helper until something expands it");

        InvariantSettled settled = InvariantSettled.settle(expandable,
                TypeChecker.symbols(expandable.module()), Map.of());

        assertFalse(clauseOf(settled.defs(), "Amount") instanceof Hir.Apply,
                "settling is what expands it, and it is what the state is named for");
    }

    private static Hir.Expr clauseOf(List<Hir.Def> defs, String named) {
        for (Hir.Def def : defs) {
            if (def.name().equals(named) && def instanceof Hir.Data data
                    && !data.invariants().isEmpty()) {
                return data.invariants().get(0).expr();
            }
        }
        return null;
    }
}
