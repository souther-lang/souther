package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

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
 * <p>{@link Expandable} and {@link InvariantSettled} are two claims about a module, and they used to
 * be one type with the tree: whichever question you asked, what came back said only that resolution
 * had been over it. A reader that wanted an expandable module and one that wanted a settled one were
 * handed the same value, and what told them apart was which query they happened to ask.
 *
 * <p>So the propositions here are about the ways in. Each state is reached by a step that performs
 * what the state claims — the cycle check, the settling — and there is no other way to reach it.
 * What that forbids is the shape this replaces: a carrier with an operation that takes a payload and
 * hands the claim back, which is a way to assert anything about anything.
 *
 * <p>That a tree is what the first of them is handed is not a hole. {@code check} answers about the
 * tree it is given, so a rewritten module is checked again rather than inheriting an answer given
 * about the tree it was rewritten from. A state saying "resolution produced this" would be a
 * record of where a value came from, and {@link Hir} already says the one thing such a state could
 * claim: no occurrence of it is one nothing has read.
 */
class AStateIsReachedOnlyThroughWhatEstablishesItTest {

    private static final List<Class<?>> STATES = List.of(Expandable.class, InvariantSettled.class);

    private static Hir.Module resolved(String source) {
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
     * The ways in, named. Each one performs what the state it answers with claims — the cycle check,
     * the settling — and that is the requirement rather than which value it is handed: a tree is a
     * fine thing to be handed by an operation that goes on to check it, and a state that took only
     * the state below would be recording where a value came from instead.
     *
     * <p>One that appears later is a way of reaching a state that someone was given, and it fails
     * here until it is either narrowed or written down as these are.
     */
    @Test
    void everyWayIntoAStateIsTheOperationThatEstablishesIt() {
        assertEquals(Set.of("check(Module, Map)"), waysInto(Expandable.class));
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
     * None of them answers with its own state. That is what {@code ResolvedModule.with} was — a
     * method on the claim that takes a payload and hands the claim back — and it is the one shape
     * that lets a state be asserted of a tree nothing established it of.
     */
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
    void theWayToAnExpandableModuleIsTheCycleCheck() {
        Hir.Module wellFounded = resolved("""
                module m exposing ( n )

                let n = 1
                """);
        assertEquals("m", Expandable.check(wellFounded, Map.of()).name());

        Hir.Module reachesItself = resolved("""
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
        Hir.Module resolved = resolved("""
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
