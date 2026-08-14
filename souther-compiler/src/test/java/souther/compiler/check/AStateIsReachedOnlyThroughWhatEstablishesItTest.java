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
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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

    private static final List<Class<?>> STATES =
            List.of(Expandable.class, InvariantSettled.class, InvariantSettled.Def.class,
                    Derived.Def.class, Derived.Module.class, Desugared.Fn.class,
                    Desugared.Module.class, Prepared.class);

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
        assertEquals(Set.of(), waysInto(InvariantSettled.Def.class),
                "a settled declaration is projected from the module it is one of");
        assertEquals(Set.of("derive(Def, Symbols)"), waysInto(Derived.Def.class));
        assertEquals(Set.of("assemble(InvariantSettled, Map)"), waysInto(Derived.Module.class));
        assertEquals(Set.of("desugar(FnDef, Symbols)"), waysInto(Desugared.Fn.class));
        assertEquals(Set.of("assemble(Module, Map)"), waysInto(Desugared.Module.class));
        assertEquals(Set.of("prepare(Module, Map)"), waysInto(Prepared.class));
    }

    /**
     * The bodies a check produced are minted where the check is, and nowhere a caller could reach.
     *
     * <p>It is not a state of the module and does not belong to this family: whether the check
     * established anything is the answer being present, which is what {@code Answer} says already.
     * What is here is the other half — the value that only a check which did establish it produces —
     * and the conjunction that makes it true is evaluated in the query that answers with it.
     */
    @Test
    void whatACheckProducedIsMintedWhereTheCheckIs() {
        Class<?> elaborated = souther.compiler.query.Bodies.Elaborated.class;

        assertEquals(0, elaborated.getConstructors().length,
                "a caller that could build one would be a caller the conjunction does not hold for");
        for (Method m : elaborated.getMethods()) {
            assertFalse(Modifier.isStatic(m.getModifiers())
                            && m.getReturnType() == elaborated,
                    "Bodies.Elaborated." + signature(m) + " is a way in that is not the check");
        }
    }

    /**
     * What a module prepares is not asked per output file.
     *
     * <p>The classes are emitted once per module, and every example row attached to it runs against
     * them, so the helpers its artifact must carry are gathered over all of those rows. Which rows
     * are reported on is asked later, where the source file is in the key. A state taking one would
     * pull an output's concern into what the module is — and would make every reader of it, the
     * checks and the adequacy report among them, answer per file.
     */
    @Test
    void whatAModulePreparesDoesNotDependOnAnOutputFile() {
        for (Method m : Prepared.class.getMethods()) {
            for (Class<?> takes : m.getParameterTypes()) {
                assertFalse(takes == String.class,
                        "Prepared." + signature(m) + " takes a name, and the only one it could be "
                                + "is an output's");
            }
        }
    }

    /**
     * A definition that has been desugared says that and no more.
     *
     * <p>The helper parameter types it carries were settled before it, by a pass whose contract is
     * best effort: a parameter its body does not determine is left as it was, for the check below to
     * report. So a state claiming they are settled would be claiming something no pass established —
     * naming a pass that ran rather than a fact a reader may lean on. What is asserted here is the
     * shape of the claim: the way in takes a definition and the symbols, and asks nothing about what
     * the definition has been through.
     */
    @Test
    void desugaringClaimsNothingAboutTheTypesADefinitionCarries() {
        Hir.Module resolved = resolved("""
                module m exposing ( Wrapped, go )

                data Wrapped = Int

                behavior go : (n: Int) -> Wrapped
                    constructs Wrapped
                let go (n) = wrap(n)
                let wrap (n) = Wrapped(n)
                """);
        Symbols scope = TypeChecker.symbols(resolved);
        Hir.FnDef unsettled = resolved.fns().stream()
                .filter(f -> f.name().equals("wrap")).findFirst().orElseThrow();

        assertTrue(unsettled.params().get(0).type() == null,
                "the parameter is open, which is a definition this state admits");
        Desugared.Fn desugared = Desugared.Fn.desugar(unsettled, scope);
        assertEquals(0, applications(bodyOf(desugared.fn())),
                "and its constructions are constructions all the same");
    }

    private static Hir.Expr bodyOf(Hir.FnDef fn) {
        return fn.body() instanceof Hir.FnBody.Written written ? written.expr() : null;
    }

    /**
     * Every route from a settled module to one of its declarations answers with a settled
     * declaration.
     *
     * <p>The constructor being closed is not enough on its own. A module handing out
     * {@link Hir.Def} would put the claim back where it was — carried by nobody — one level down,
     * and the reader that needs it is the measured one: the rewrite of what a declaration says does
     * different work depending on whether its clauses have been expanded, and says nothing about the
     * difference.
     */
    @Test
    void noRouteToADeclarationOfASettledModuleHandsOverANode() {
        for (Method m : InvariantSettled.class.getMethods()) {
            assertFalse(mentions(m.getGenericReturnType(), Hir.Def.class),
                    "InvariantSettled." + signature(m) + " hands over a declaration node");
        }
    }

    private static boolean mentions(java.lang.reflect.Type type, Class<?> named) {
        if (type == named) {
            return true;
        }
        if (type instanceof java.lang.reflect.ParameterizedType parameterized) {
            for (java.lang.reflect.Type argument : parameterized.getActualTypeArguments()) {
                if (mentions(argument, named)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * And deriving one is what writes the constructions in what it says as constructions — the
     * reading that made the declaration its own state.
     */
    @Test
    void theWayToADerivedDeclarationIsTheRewrite() {
        Hir.Module resolved = resolved("""
                module m exposing ( Amount, Wrapped )

                data Wrapped = Int
                data Amount = Int
                    invariant isOk(value)

                let isOk (n: Int) : Bool = Wrapped(n) == Wrapped(0)
                """);
        Symbols scope = TypeChecker.symbols(resolved);
        InvariantSettled settled =
                InvariantSettled.settle(Expandable.check(resolved, Map.of()), scope, Map.of());
        InvariantSettled.Def amount = settled.defs().stream()
                .filter(d -> d.name().equals("Amount")).findFirst().orElseThrow();

        assertEquals(2, applications(clauseOf(List.of(amount.def()), "Amount")),
                "the constructions are written as applications until this rewrites them");
        assertEquals(0, applications(clauseOf(List.of(Derived.Def.derive(amount, scope).read()),
                        "Amount")),
                "and none is left as one afterwards");
    }

    /**
     * And an assembly is handed the answers for its own parts, which it checks rather than reads off
     * the key they arrived under.
     *
     * <p>The map is keyed by bare name, and a bare name is a name in some module: two modules writing
     * `Amount` write two declarations, and an answer for one of them put under `"Amount"` would
     * otherwise be built into the other. What comes out would say `module a` and hold `b.Amount`,
     * which is the proposition — every declaration this module writes has an answer — made of a
     * declaration this module does not write.
     *
     * <p>The query graph asks {@code Shapes.Derived} and {@code Shapes.DerivedDeclarations} with the
     * same module name, so nothing here goes wrong today. That is the reason to hold it: a claim that
     * stands because its callers are careful is a claim nobody is keeping.
     */
    @Test
    void anAssemblyRefusesAnAnswerForAnotherModulesDeclaration() {
        Symbols scopeA = TypeChecker.symbols(resolvedA());
        InvariantSettled a = InvariantSettled.settle(
                Expandable.check(resolvedA(), Map.of()), scopeA, Map.of());
        Symbols scopeB = TypeChecker.symbols(resolvedB());
        InvariantSettled b = InvariantSettled.settle(
                Expandable.check(resolvedB(), Map.of()), scopeB, Map.of());

        Derived.Def ofA = Derived.Def.derive(defNamed(a, "Amount"), scopeA);
        Derived.Def ofB = Derived.Def.derive(defNamed(b, "Amount"), scopeB);
        assertEquals("Amount", ofB.name(), "the same bare name, so the map key does not tell them apart");
        assertNotEquals(ofA.declaredKey(), ofB.declaredKey());

        assertEquals("a", Derived.Module.assemble(a, Map.of("Amount", ofA)).name());
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> Derived.Module.assemble(a, Map.of("Amount", ofB)));
        assertTrue(refused.getMessage().contains("Amount"), refused.getMessage());
    }

    /** The same of the definitions, which a module carries several modules' of under names of one
     *  shape — so the key tells them apart even less there. */
    @Test
    void anAssemblyRefusesAnAnswerForAnotherModulesDefinition() {
        Symbols scopeA = TypeChecker.symbols(resolvedA());
        Derived.Module a = Derived.Module.assemble(
                InvariantSettled.settle(Expandable.check(resolvedA(), Map.of()), scopeA, Map.of()),
                Map.of("Amount", Derived.Def.derive(defNamed(InvariantSettled.settle(
                        Expandable.check(resolvedA(), Map.of()), scopeA, Map.of()), "Amount"), scopeA)));
        Hir.FnDef ofA = a.fns().get(0);
        Hir.FnDef ofB = new Hir.FnDef(ofA.written(), "b", ofA.params(), ofA.declaredReturn(),
                ofA.body(), ofA.modifiers(), ofA.pos());

        assertEquals(ofA.name(), ofB.name(), "the same bare name, so the map key does not tell them apart");
        assertEquals("a", Desugared.Module.assemble(a,
                Map.of(ofA.name(), Desugared.Fn.desugar(ofA, scopeA))).name());
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> Desugared.Module.assemble(a,
                        Map.of(ofA.name(), Desugared.Fn.desugar(ofB, scopeA))));
        assertTrue(refused.getMessage().contains(ofA.name()), refused.getMessage());
    }

    private static Hir.Module resolvedA() {
        return resolved("""
                module a exposing ( Amount )

                data Amount = Int

                let ok (n: Int) : Bool = n > 0
                """);
    }

    private static Hir.Module resolvedB() {
        return resolved("""
                module b exposing ( Amount )

                data Amount = Int
                """);
    }

    private static InvariantSettled.Def defNamed(InvariantSettled settled, String name) {
        return settled.defs().stream().filter(d -> d.name().equals(name)).findFirst().orElseThrow();
    }

    private static int applications(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] found = {e instanceof Hir.Apply ? 1 : 0};
        Hir.forEachChild(e, c -> found[0] += applications(c));
        return found[0];
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

        assertFalse(clauseOf(settled.defs().stream().map(InvariantSettled.Def::def).toList(),
                        "Amount") instanceof Hir.Apply,
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
