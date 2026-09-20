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
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    @Test
    void theTwoExpansionsStandInsideTwoBuilds() {
        String source = HEAD + """
                behavior f : (n: Int) -> Int
                let f (n) = (if n > 0 then viaCall else 0) + (if n > 1 then viaCall else 0)
                """;
        Set<BindingOwner> owners = new LinkedHashSet<>();
        collect(Compiler.compiled(source, "m").db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().writtenBody(), owners);

        assertEquals(2, owners.size(), owners::toString);
        assertTrue(owners.stream().allMatch(each ->
                each instanceof BindingOwner.Expansion it && it.within() instanceof BindingOwner.Build),
                owners::toString);
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
