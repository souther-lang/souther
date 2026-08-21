package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.HelperGraph;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.HelperTable;
import souther.compiler.check.InliningPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.BindingOwner;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An expansion knows which recursions it could not remove, and says so.
 *
 * <p>A call to a helper that recurses is left as a call — expanding it would not terminate — so a
 * method of that name has to be emitted wherever the tree ends up. That is a requirement, and the
 * expansion is what makes it. Worked out instead by walking the places a module writes expressions,
 * the answer was a prediction about work not yet done, and it was wrong for every place the walk did
 * not know about.
 *
 * <p>The requirement is made at the decision, not at a shape. A recursion written where a value goes
 * is eta-expanded into a call before anything else happens to it, so both the call and the value
 * reach the one place that decides to leave a call standing. Held here so that a change to how a
 * function reference is represented fails this rather than quietly collecting fewer requirements:
 * what has to stay true is that a recursion surviving into the tree is a recursion this answers
 * with, however it was written.
 */
class AnExpansionAnswersWithTheRecursionsItLeftStandingTest {

    private static final String CALLED = """
            module called

            data Emp = { boss: Emp? }

            let depth (e: Emp) : Int =
                match e.boss with
                    | Some b -> 1 + depth(b)
                    | None   -> 0

            let deep (e: Emp) : Bool = depth(e) > 3
            """;

    private static final String AS_A_VALUE = """
            module handed

            data Emp = { boss: Emp? }

            let depth (e: Emp) : Int =
                match e.boss with
                    | Some b -> 1 + depth(b)
                    | None   -> 0

            let all (es: List<Emp>) : List<Int> = List.map(depth, es)
            """;

    private static final String NEITHER = """
            module neither

            let twice (n: Int) : Int = n * 2

            let four (n: Int) : Int = twice(twice(n))
            """;

    /** What expanding {@code fn}'s body of {@code module} left standing. */
    private static Set<String> leftStandingIn(String module, String source, String fn) {
        Db db = Compilation.ofDocuments(Map.of(module + ".sou", source), Set.of(), ModulePath.EMPTY)
                .db();
        HelperTable table = db.ask(new Bodies.Expanding(module, InliningPolicy.FULL)).value().table();
        Hir.FnDef def = HelperInliner.helpersOf(db.ask(new Bodies.Settled(module)).value()).get(fn);
        assertTrue(def != null, fn + " is a helper of " + module);

        HelperInliner inliner = HelperInliner.over(table, HelperGraph.of(table));
        inliner.inline(def.writtenBody(), new BindingOwner.OfValue(module, fn));
        return inliner.leftStanding();
    }

    @Test
    void aRecursionCalledIsAnsweredWith() {
        assertEquals(Set.of("depth"), leftStandingIn("called", CALLED, "deep"));
    }

    /** The same recursion handed to a combinator rather than called. */
    @Test
    void andSoIsOneHandedOverAsAValue() {
        Set<String> standing = leftStandingIn("handed", AS_A_VALUE, "all");

        assertTrue(standing.contains("depth"),
                "a recursion reaches the tree however it was written, and left: " + standing);
    }

    /**
     * And the library's own, which the combinator became. A body that folds holds a call to the one
     * recursion the library has, whether or not anything else in the module reaches it.
     */
    @Test
    void andTheLibrarysOwnWhereACombinatorBecameAFold() {
        assertTrue(leftStandingIn("handed", AS_A_VALUE, "all").contains("List.foldFrom"),
                leftStandingIn("handed", AS_A_VALUE, "all").toString());
    }

    /** An expansion that removed everything answers with nothing. */
    @Test
    void anExpansionThatRemovedEverythingAnswersWithNothing() {
        assertEquals(Set.of(), leftStandingIn("neither", NEITHER, "four"));
    }
}
