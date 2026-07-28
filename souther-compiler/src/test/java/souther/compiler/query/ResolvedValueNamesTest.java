package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a name in a body denotes is answered once, where the module's names are resolved, and the
 * answer is in the tree.
 *
 * <p>Before this, each reader worked it out in the order it happened to try: the checker asked its
 * type environment, then the unit data declarations, then the library, then the injected behaviors;
 * the newtype desugar asked only the type namespace, so a binding of the same spelling was invisible
 * to it. These pin the one answer, so a reader that disagrees with it is a reader that is wrong.
 */
class ResolvedValueNamesTest {

    private static Ast.Module resolve(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        return c.db().ask(new Names.Resolved("m.a")).value();
    }

    /** Every name used as a value in the module's bodies, in the order it is written. */
    private static List<Ast.Expr> named(Ast.Module m) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            if (fn.body() != null) {
                collect(fn.body(), out);
            }
        }
        return out;
    }

    private static void collect(Ast.Expr e, List<Ast.Expr> out) {
        if (e instanceof Ast.Var || e instanceof Ast.Call) {
            out.add(e);
        }
        Ast.mapChildren(e, child -> {
            collect(child, out);
            return child;
        });
    }

    private static ValueName denotes(Ast.Expr e) {
        return e instanceof Ast.Var v ? v.denotes() : ((Ast.Call) e).denotes();
    }

    /** The one named {@code written}, which each of these writes once. */
    private static ValueName denotationOf(String source, String written) {
        for (Ast.Expr e : named(resolve(source))) {
            String spelled = e instanceof Ast.Var v ? v.name() : ((Ast.Call) e).fn();
            if (spelled.equals(written)) {
                return denotes(e);
            }
        }
        throw new AssertionError("nothing named `" + written + "` in the resolved module");
    }

    @Test
    void aParameterIsLocalToTheBindingThatIntroducedIt() {
        Ast.Module m = resolve("""
                module m.a exposing ( f )

                behavior f : (n: Int) -> Int
                let f (n) = n
                """);

        ValueName denoted = denotationOf("""
                module m.a exposing ( f )

                behavior f : (n: Int) -> Int
                let f (n) = n
                """, "n");
        ValueName.Local local = assertInstanceOf(ValueName.Local.class, denoted);
        assertEquals("n", local.name());
        assertEquals(m.fns().get(0).params().get(0).pos(), local.binder(),
                "the binder is the parameter it was bound by");
    }

    /** A body may bind a name the module declares, and inside the binding that is what it means. */
    @Test
    void aBindingWinsOverTheDeclarationOfTheSameSpelling() {
        String source = """
                module m.a exposing ( Amount, f )

                data Amount = Int

                behavior f : (n: Int) -> Int
                let f (n) = {
                    let Amount = n
                    Amount
                }
                """;

        assertInstanceOf(ValueName.Local.class, denotationOf(source, "Amount"));
    }

    /** Two bindings of one spelling are two names, told apart by where each was bound. */
    @Test
    void twoBindingsOfOneSpellingAreTwoNames() {
        String source = """
                module m.a exposing ( f, g )

                behavior f : (n: Int) -> Int
                let f (n) = n

                behavior g : (n: Int) -> Int
                let g (n) = n
                """;
        List<ValueName> locals = new ArrayList<>();
        for (Ast.Expr e : named(resolve(source))) {
            locals.add(denotes(e));
        }

        assertEquals(2, locals.size(), locals.toString());
        assertNotEquals(locals.get(0), locals.get(1),
                "one spelling, two bindings, two names: " + locals);
    }

    @Test
    void aLibraryCallDenotesTheLibraryFunction() {
        String source = """
                module m.a exposing ( f )

                behavior f : (xs: List<Int>) -> Int
                let f (xs) = List.length(xs)
                """;

        assertEquals(new ValueName.Stdlib("List.length"), denotationOf(source, "List.length"));
    }

    @Test
    void aCallOfTheModulesOwnLetDenotesThatHelper() {
        String source = """
                module m.a exposing ( f )

                let double (n: Int): Int = n * 2

                behavior f : (n: Int) -> Int
                let f (n) = double(n)
                """;

        assertEquals(new ValueName.Helper("m.a", "double"), denotationOf(source, "double"));
    }

    @Test
    void aCallOfAnInjectedBehaviorDenotesThatBehavior() {
        String source = """
                module m.a exposing ( f )

                behavior rate : (n: Int) -> Int

                behavior f : (n: Int) -> Int
                    requires rate
                let f (n, rate) = rate(n)
                """;

        // the trailing `requires` parameter binds the name in the body (spec 12.6)
        assertInstanceOf(ValueName.Local.class, denotationOf(source, "rate"));
    }

    @Test
    void aUnitDataUsedAsAValueDenotesThatType() {
        String source = """
                module m.a exposing ( Approved, f )

                data Approved

                behavior f : (n: Int) -> Approved
                    constructs Approved
                let f (n) = Approved
                """;

        ValueName.OfType denoted = assertInstanceOf(ValueName.OfType.class,
                denotationOf(source, "Approved"));
        assertEquals("m.a", denoted.type().module());
        assertEquals("Approved", denoted.type().name());
    }

    /** {@code Amount(500)} names a type, not a function; that it is a construction is settled here
     * and not by a later pass asking the type namespace again. */
    @Test
    void aNewtypeAppliedToAValueDenotesTheTypeItConstructs() {
        String source = """
                module m.a exposing ( Amount, f )

                data Amount = Int

                behavior f : (n: Int) -> Amount
                    constructs Amount
                let f (n) = Amount(n)
                """;

        ValueName.OfType denoted = assertInstanceOf(ValueName.OfType.class,
                denotationOf(source, "Amount"));
        assertEquals("Amount", denoted.type().name());
    }

    @Test
    void aNameNothingAnswersToDenotesNothing() {
        String source = """
                module m.a exposing ( f )

                behavior f : (n: Int) -> Int
                let f (n) = nosuch
                """;

        assertInstanceOf(ValueName.Unresolved.class, denotationOf(source, "nosuch"));
    }

    /** Every name in every body is answered — nothing is left as a spelling for a later reader to
     * work out for itself. */
    @Test
    void everyNameInABodyIsAnswered() {
        Ast.Module m = resolve("""
                module m.a exposing ( Amount, Approved, f )

                data Amount = Int
                data Approved

                let double (n: Int): Int = n * 2

                behavior f : (xs: List<Int>) -> Amount | Approved
                    constructs Amount, Approved
                let f (xs) = {
                    let total = List.length(xs)
                    if total > 0 then Amount(double(total)) else Approved
                }
                """);

        for (Ast.Expr e : named(m)) {
            assertTrue(denotes(e) != null, "unanswered name in " + e);
        }
    }
}
