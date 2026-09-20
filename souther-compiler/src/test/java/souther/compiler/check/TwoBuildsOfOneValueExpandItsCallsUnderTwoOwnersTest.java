package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.types.BindingOwner;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value built for two regions expands the helpers its body calls once per build, and each
 * expansion writes its bindings under its own owner.
 *
 * <p>The two builds are two copies of one written body, so a call in it is one site and two
 * expansions. Written under the owner of the region the builds stand in, both expansions would own
 * the same bindings, and the numbering of a behavior's bindings would meet one binding at two
 * places.
 */
class TwoBuildsOfOneValueExpandItsCallsUnderTwoOwnersTest {

    private static final String HEAD = """
            module m exposing (f)

            let same (n: Int) : Int = n

            let viaCall = same(1)

            """;

    private static void accepted(String tail) {
        assertEquals("{0=[]}", String.valueOf(Compiler.compiled(HEAD + tail, "m").diagnostics()));
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoForks() {
        accepted("""
                behavior f : (n: Int) -> Int
                let f (n) = (if n > 0 then viaCall else 0) + (if n > 1 then viaCall else 0)
                """);
    }

    @Test
    void oneValueNamedOnTheRightOfTwoShortCircuits() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (n > 0 && viaCall > 0) || (n > 1 && viaCall > 0)
                """);
    }

    @Test
    void aValueWhoseBodyNamesAnotherThatCallsAHelper() {
        accepted("""
                let outer = same(viaCall) + 1

                behavior f : (n: Int) -> Int
                let f (n) = (if n > 0 then outer else 0) + (if n > 1 then outer else 0)
                """);
    }

    /**
     * A build made inside a helper's expansion, which is itself expanded twice: the expansion is
     * inside a build and the build is inside an expansion.
     *
     * <p>The two builds are one value for one region of one written body, so only the copy of the
     * helper they stand in tells them apart.
     */
    @Test
    void aBuildInsideTwoExpansionsOfOneHelper() {
        accepted("""
                let helper (n: Int) : Int = if n > 0 then viaCall else 0

                behavior f : (n: Int) -> Int
                let f (n) = helper(n) + helper(n)
                """);
    }

    @Test
    void aBuildInsideTwoExpansionsOfALibraryOperation() {
        accepted("""
                let bigger (m: Int) : Bool = m > viaCall

                behavior f : (n: Int) -> Bool
                let f (n) = List.any(bigger, [n]) || List.any(bigger, [n + 1])
                """);
    }

    /**
     * A value that needs another at its root region is emitted as a method taking it, so the calls in
     * its body are expanded once, in that body, and not once per build of it.
     */
    @Test
    void theCallsInAValuesBodyAreExpandedOnceInThatBody() {
        String source = HEAD + """
                let dependent = same(viaCall)

                behavior f : (n: Int) -> Int
                let f (n) = (if n > 0 then dependent else 0) + (if n > 1 then dependent else 0)
                """;
        var db = Compiler.compiled(source, "m").db();
        Set<BindingOwner> inTheBehavior = new LinkedHashSet<>();
        collect(db.ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().writtenBody(), inTheBehavior);
        Set<BindingOwner> inTheValue = new LinkedHashSet<>();
        collect(db.ask(new Bodies.LoweredBody("m", new DefinitionName("dependent")))
                .value().value().writtenBody(), inTheValue);

        assertEquals(0, inTheBehavior.size(), inTheBehavior::toString);
        assertEquals(1, inTheValue.size(), inTheValue::toString);
    }

    /** What each expansion of {@code same} in {@code e} is owned by. */
    private static void collect(Hir.Expr e, Set<BindingOwner> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Hir.Expansion it && it.callee().name().equals("same")) {
            out.add(it.application());
        }
        Hir.forEachChild(e, child -> collect(child, out));
    }
}
