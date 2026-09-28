package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value named on every way out of a fork is built at the fork, and so once.
 *
 * <p>A region is somewhere entered on some paths and not others, and a value is bound at the head
 * of the region that demands it so that it is evaluated where a reference to it would have been. A
 * fork's arms are ways out of one place: whichever is taken, one of them is — so a value every arm
 * names is named on every path through the fork, and binding it around the fork rather than in each
 * arm moves no work onto a path that had none.
 *
 * <p>What the arms would cost is two builds of one written construct. Everything that files an
 * answer about a construct addresses it by what the source wrote and which copies it stands in, so
 * two builds of one value's body in one behavior are two nodes one address reaches, and the
 * enumeration of a module's comparisons refuses the pair rather than answer either reader with the
 * other's.
 *
 * <p>Counted over the tree the backend emits from: the build of the value stands once in it,
 * whichever of these the body is.
 */
class AValueEveryWayOutNamesIsBuiltAtTheForkTest {

    private static final String HEAD = """
            module m exposing (f, Kind)

            data Kind = Yes | No

            let over = List.length([1, 2, 3]) > 2

            """;

    /** How many of the comparisons `over` writes stand in the body the backend emits from. */
    private static int comparisonsOfTheValue(String tail) {
        Compilation compiled = Compiler.compiled(HEAD + tail, "m");
        assertEquals("{0=[]}", String.valueOf(compiled.diagnostics()),
                "the source this counts over was refused");
        Hir.Expr body = compiled.db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().definition().writtenBody();
        return count(body);
    }

    private static int count(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {written(e) ? 1 : 0};
        Hir.forEachChild(e, child -> held[0] += count(child));
        return held[0];
    }

    /** A build of `over`: the body the backend emits from calls the method the value is emitted as,
     *  so what stands in it is one reference per build and not the value's comparison. */
    private static boolean written(Hir.Expr e) {
        return e instanceof Hir.ValueInvocation call && call.value().toString().endsWith("over");
    }

    @Test
    void aValueBothArmsOfAnIfNameIsBuiltOnce() {
        assertEquals(1, comparisonsOfTheValue("""
                behavior f : (n: Int) -> Bool
                let f (n) = if n > 0 then over else over
                """));
    }

    /** The same of a match, whose arms are the ways out of one scrutinee. */
    @Test
    void aValueEveryArmOfAMatchNamesIsBuiltOnce() {
        assertEquals(1, comparisonsOfTheValue("""
                behavior f : (k: Kind) -> Bool
                let f (k) =
                  match k with
                    | Yes -> over
                    | No -> over
                """));
    }

    /**
     * And a value one region names twice is built once there, which is what the region rule says
     * without the fork rule being asked.
     */
    @Test
    void aValueOneRegionNamesTwiceIsBuiltOnce() {
        assertEquals(1, comparisonsOfTheValue("""
                behavior f : (n: Int) -> List<Bool>
                let f (n) = [over, over]
                """));
    }
}
