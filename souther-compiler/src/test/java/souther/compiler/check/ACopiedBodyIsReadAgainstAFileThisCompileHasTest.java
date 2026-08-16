package souther.compiler.check;

import souther.compiler.source.SourceId;
import souther.compiler.diag.QuotedFrom;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.Placement;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two things a body carries once it has been copied into somewhere else, and which of them each
 * answers.
 *
 * <p>A body is spliced into everything that calls it. Where it came from a source this compile
 * holds, the copy keeps the positions it was written at. Where it did not — the standard library, a
 * module read back off the module path — those positions name a file nobody holds, so the copy is
 * given the call site, and every rule checked on it reports at a coordinate in the caller's file.
 *
 * <p>Two claims, and they are separate. Every coordinate a check reads is one this compile can quote,
 * or a report lands on a line the reader is not looking at. And a coordinate that was given rather
 * than written says so, all the way down to what the backend is built from — or a rule reported from
 * there states its subject is at a place it is not, which nothing about the coordinate could
 * contradict.
 */
class ACopiedBodyIsReadAgainstAFileThisCompileHasTest {

    /** A body that reaches the standard library, whose source no compile of a user model has. */
    private static final String OVER_THE_LIBRARY = """
            module demo

            data Kept
            data Dropped
            data Mark = Kept | Dropped

            data Item = { mark: Mark }

            let kept (items: List<Item>): Int =
                List.length(List.filter(i -> i.mark == Kept, items))
            """;

    private static final String DECLARING = """
            module up exposing ( doubled )
            let doubled (x: Int): Int = x + x
            """;

    private static final String IMPORTING = """
            module down
            import up ( doubled )

            data Count = Int
                invariant value >= 0

            behavior twice : (n: Int) -> Count
                constructs Count
            let twice (n) = Count(doubled(n))
            """;

    // --- every coordinate a check reads is one this compile can quote ---------------------------

    @Test
    void everyPositionInAnExpandedBodyNamesASourceThisCompileHas() {
        List<SourcePos> positions = positionsIn(expanded(OVER_THE_LIBRARY, "kept"));

        List<SourcePos> nowhere = positions.stream().filter(p -> !(p.quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds)).toList();
        assertEquals(List.of(), nowhere,
                "a copy read against the caller's file carries coordinates of that file");
    }

    /** And the walk is looking at copied nodes while it says so: a body holding none would pass this
     *  by having nothing to be wrong about. */
    @Test
    void andSomeOfThemWereCopiedFromOutOfSight() {
        List<SourcePos> positions = positionsIn(expanded(OVER_THE_LIBRARY, "kept"));

        assertFalse(positions.stream().noneMatch(SourcePos::isOutOfSight),
                "the fixture expands a library body, so some of what was walked came from one");
    }

    /** The other half of the same rule: a body whose source this compile does have keeps the
     *  positions it was written at, so nothing about it stands in for anything. */
    @Test
    void aBodyThisCompileHasTheSourceOfIsNotStoodInFor() {
        List<SourcePos> positions = positionsIn(coreOf(
                Map.of("down.sou", IMPORTING, "up.sou", DECLARING), ModulePath.EMPTY,
                "down", "twice"));

        assertTrue(positions.stream().anyMatch(p -> p.isIn(new SourceId("up.sou"))),
                "the imported body was spliced in, keeping the file it was written in");
        assertEquals(List.of(), positions.stream().filter(SourcePos::isOutOfSight).toList(),
                "a place this compile can show is not a place anything stands in for");
    }

    // --- and the answer survives being lowered --------------------------------------------------

    /**
     * What the backend is built from carries it too. {@code Core} keeps a coordinate and no expansion
     * structure, so a rule checked there — the invariant-discharge reader, which reports at a
     * construction — has the coordinate and nothing else to ask.
     */
    @Test
    void aCoordinateGivenToACopyStillSaysSoInCore() {
        List<SourcePos> positions = positionsIn(coreOf(Map.of("down.sou", IMPORTING),
                published(DECLARING), "down", "twice"));

        assertEquals(List.of(), positions.stream().filter(p -> !(p.quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds)).toList(),
                "every coordinate the backend is built from names a source this compile has");
        Placement spliced = Placement.aFileOfThisCompile(new SourceId("down.sou"))
                .standingInFor(Placement.whatAModulePublished(
                        new SourceProvenance.APublishedModule("up", "up.doubled")));
        assertTrue(positions.stream().anyMatch(p -> spliced.equals(p.placement())),
                "the body came from a module read off the path, and the lowering did not forget");
    }

    // --- the fixtures ---------------------------------------------------------------------------

    /** {@code behavior}'s body with every helper call expanded, as a check downstream reads it. */
    private static Hir.Expr expanded(String source, String fn) {
        var parsed = CstFrontend.parseWithSlices(source, null, new SourceId("demo.sou"));
        Hir.Module module = Resolve.module(parsed.module(), SyntaxSymbols.of(parsed.module()));
        HelperInliner inliner = HelperInliner.forModule(module);
        Hir.FnDef body = inliner.held().get(fn);
        assertNotNull(body, "the fn under test is one of the module's own");
        return inliner.inline(body.writtenBody(), inliner.bodyOf(fn));
    }

    private static Core coreOf(Map<String, String> sources, ModulePath path, String module,
                               String behavior) {
        Compilation compilation = Compilation.ofDocuments(sources, Set.of(), path);
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        return body;
    }

    /** The declaring module as another project built it: classes alone, no source. */
    private static ModulePath published(String source) {
        Map<String, byte[]> classes = Compiler.compileModules(List.of(source));
        return classes::get;
    }

    private static List<SourcePos> positionsIn(Hir.Expr e) {
        List<SourcePos> out = new ArrayList<>();
        walk(e, out);
        return out;
    }

    private static void walk(Hir.Expr e, List<SourcePos> out) {
        if (e.pos() != null) {
            out.add(e.pos());
        }
        Hir.forEachChild(e, c -> walk(c, out));
    }

    private static List<SourcePos> positionsIn(Core e) {
        List<SourcePos> out = new ArrayList<>();
        walk(e, out);
        return out;
    }

    private static void walk(Core e, List<SourcePos> out) {
        if (e.pos() != null) {
            out.add(e.pos());
        }
        Core.forEachChild(e, c -> walk(c, out));
    }
}
