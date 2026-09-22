package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.RegionSlot;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The tree keeps which build of a value each one is, so that a walk that knows which copy it is in
 * can say it.
 *
 * <p>The pass that shares builds knows the region a value is built for and not the copy of a body
 * it is walking in. What it settled is left in the tree as a {@link Hir.Materialised} around the
 * value it binds, and the order builds nest in is the order a later walk meets them: a value built
 * inside another's body sits inside that node, one built beside it sits beside it, and the call of a
 * helper is a node of its own that opens no region.
 *
 * <p>Read off the lowered body and nothing later, because what these are about is what the tree
 * holds and not what a reader made of it.
 */
class AValueBuiltMoreThanOnceKeepsWhichBuildEachIsTest {

    private static final String HEAD = """
            module m exposing (f, Kind)

            data Kind = Yes | No

            let inner = List.length([1, 2, 3]) > 2

            let outer = if List.length([1]) > 0 then inner else false

            let same (n: Int) : Bool = n > 0

            let viaCall = same(1)

            """;

    private static Hir.Expr lowered(String tail) {
        return loweredDefinition(tail, "f");
    }

    /** The body the backend emits for {@code name}: a behavior, or a value emitted as a method. */
    private static Hir.Expr loweredDefinition(String tail, String name) {
        Compilation compilation = Compilation.ofSource(HEAD + tail, "m");
        return compilation.db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName(name)))
                .value().value().definition().writtenBody();
    }

    /** A build of a value, whether it carries the body or calls the method the value is emitted as. */
    private record Build(ValueName value, MaterialisationSite site) { }

    /** Every build in the tree, outermost first and left to right. */
    private static List<Build> builds(Hir.Expr e) {
        List<Build> out = new ArrayList<>();
        collect(e, out);
        return out;
    }

    private static void collect(Hir.Expr e, List<Build> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Hir.Materialised built) {
            out.add(new Build(built.value(), built.site()));
        }
        if (e instanceof Hir.ValueInvocation call) {
            out.add(new Build(call.value(), call.site()));
        }
        Hir.forEachChild(e, child -> collect(child, out));
    }

    private static List<Build> buildsOf(String value, List<Build> all) {
        return all.stream().filter(each -> each.value().toString().endsWith(value)).toList();
    }

    @Test
    void aValueBuiltForTheBodyIsBuiltForTheDefinitionThatIsWritten() {
        List<Build>all = builds(lowered("""
                behavior f : (n: Int) -> Bool
                let f (n) = inner
                """));

        assertEquals(1, all.size());
        assertInstanceOf(MaterialisationSite.Body.class, all.get(0).site());
    }

    @Test
    void aValueBuiltInAnArmIsBuiltForThatArm() {
        List<Build>all = builds(lowered("""
                behavior f : (n: Int) -> Bool
                let f (n) = if n > 0 then inner else false
                """));

        assertEquals(1, all.size());
        MaterialisationSite.Slot site = assertInstanceOf(MaterialisationSite.Slot.class,
                all.get(0).site());
        assertInstanceOf(RegionSlot.IfThen.class, site.slot());
    }

    @Test
    void aValueBuiltInsideAnotherValuesForkIsBuiltInThatValuesOwnBody() {
        String source = """
                behavior f : (n: Int) -> Bool
                let f (n) = if n > 0 then outer else false
                """;
        List<Build>all = builds(lowered(source));

        // The behavior calls the method `outer` is emitted as, and holds no build of `inner`: that
        // one is built where `outer` names it, inside `outer`'s own body.
        assertEquals(1, buildsOf("outer", all).size());
        assertEquals(0, buildsOf("inner", all).size());
        List<Build>insideOuter =
                buildsOf("inner", builds(loweredDefinition(source, "outer")));
        assertEquals(1, insideOuter.size());
        MaterialisationSite.Slot site = assertInstanceOf(MaterialisationSite.Slot.class,
                insideOuter.get(0).site());
        assertInstanceOf(RegionSlot.IfThen.class, site.slot());
    }

    /**
     * Two builds of one value are two nodes, and what tells them apart is the region each was built
     * for. What the value builds inside its own fork is built once, in the value's own body, and is
     * the same for both.
     */
    @Test
    void twoBuildsOfOneValueAreToldApartByTheRegionAndTheirInnerBuildIsOne() {
        String source = """
                behavior f : (n: Int) -> Bool
                let f (n) = (if n > 0 then outer else false) || (if n > 1 then outer else false)
                """;
        List<Build>all = builds(lowered(source));

        List<Build>outer = buildsOf("outer", all);
        assertEquals(2, outer.size());
        assertNotEquals(outer.get(0).site(), outer.get(1).site());
        assertEquals(0, buildsOf("inner", all).size());
        assertEquals(1, buildsOf("inner", builds(loweredDefinition(source, "outer"))).size());
    }

    @Test
    void aValueWhoseBodyCallsAHelperHoldsTheCallInItsOwnBody() {
        String source = """
                behavior f : (n: Int) -> Bool
                let f (n) = viaCall
                """;
        List<Build>all = builds(lowered(source));

        assertEquals(1, all.size());
        assertFalse(holdsAnExpansion(lowered(source)),
                "the behavior calls the value's method and holds no call of the helper");
        assertTrue(holdsAnExpansion(loweredDefinition(source, "viaCall")),
                "the call of the helper stands in the body of the value that makes it");
    }

    private static boolean holdsAnExpansion(Hir.Expr e) {
        boolean[] found = {false};
        walk(e, found);
        return found[0];
    }

    private static void walk(Hir.Expr e, boolean[] found) {
        if (e == null || found[0]) {
            return;
        }
        if (e instanceof Hir.Expansion) {
            found[0] = true;
            return;
        }
        Hir.forEachChild(e, child -> walk(child, found));
    }

    /**
     * A region written inside a helper is one region of the source however many copies of the helper
     * there are, so its builds carry the same site in every copy. Which copy is the call's to say,
     * and the site says nothing of it.
     */
    @Test
    void aRegionWrittenInsideAHelperIsTheSameSiteInEveryCopy() {
        List<Build>all = builds(lowered("""
                let named (n: Int) : Bool = n > 0 && inner

                behavior f : (n: Int) -> Bool
                let f (n) = named(n) || named(n + 1)
                """));

        List<Build>inner = buildsOf("inner", all);
        assertEquals(2, inner.size());
        MaterialisationSite.Slot site = assertInstanceOf(MaterialisationSite.Slot.class,
                inner.get(0).site());
        assertInstanceOf(RegionSlot.ShortCircuitRight.class, site.slot());
        assertEquals(inner.get(0).site(), inner.get(1).site());
    }

    /**
     * The body of a call is no region: a value the copy names outside any region of its own is
     * demanded by the region the call stands in, so two calls of one helper build it once there.
     */
    @Test
    void theBodyOfACallOpensNoRegion() {
        List<Build>all = builds(lowered("""
                let named (n: Int) : Bool = inner

                behavior f : (n: Int) -> Bool
                let f (n) = named(n) || named(n + 1)
                """));

        assertEquals(1, all.size());
        assertInstanceOf(MaterialisationSite.Body.class, all.get(0).site());
    }
}
