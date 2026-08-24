package souther.compiler;

import souther.compiler.source.SourceId;
import souther.compiler.diag.QuotedFrom;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.Resolve;
import souther.compiler.check.SyntaxSymbols;
import souther.compiler.diag.SourcePos;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.meta.ModuleReadback;
import souther.compiler.meta.ReadableModule;
import souther.compiler.meta.Readback;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether the code a position names is written where a reader can be shown it is decided by whoever
 * handed the text over, at the moment the text becomes positions, and by nothing downstream.
 *
 * <p>It used to be decided downstream, twice. The pass that splices a body into its callers asked
 * whether this compile could quote the place, and before that which module declared the body; a
 * reader of finished reports had nothing left to ask at all, which is why #756's attempt to drop
 * second regions naming no source was withdrawn. Between those two, what stood for the answer was a
 * position naming no source — a spelling that already means something else for a label, and that a
 * text nobody has named carries for a different reason entirely.
 *
 * <p>So the two questions are held apart here. Which source a line and a column are read in, and
 * whether that is where the code is, are separate components with separate answers, and neither is
 * inferred from the other. The witness is a body copied in from out of sight: it is out of sight and
 * in a source of this compile at once.
 */
class WhetherCodeIsOutOfSightIsSettledWhereItIsParsedTest {

    // --- what the parse settles -----------------------------------------------------------------

    /**
     * The standard library ships with the compiler and is in no source of any compile that calls it.
     * Every position of it says so where it is declared, before anything has been spliced anywhere.
     */
    @Test
    void everyPositionOfTheStandardLibraryIsOutOfSight() {
        List<SourcePos> positions = new ArrayList<>();
        DefaultStdlib.get().helpers().values().forEach(fn -> collect(fn.writtenBody(), positions));

        assertFalse(positions.isEmpty(), "the library has bodies to have positions in");
        assertEquals(List.of(), positions.stream().filter(p -> !(p.quotedFrom() instanceof QuotedFrom.TextItCannotShow)).toList(),
                "a library body is written where no compile that calls it holds a file");
        assertEquals(List.of(), positions.stream().filter(p -> p.quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds).toList(),
                "and there is no file of this compile for it to be in");
    }

    /**
     * A module read back off the module path is parsed from a text put back together out of what it
     * published. Line 4 of that text exists; nobody holds a file it is line 4 of.
     */
    @Test
    void everyPositionOfAModuleReadOffThePathIsOutOfSight() {
        Map<String, byte[]> classes = Compiler.compileModules(List.of("""
                module lib.rule exposing ( Code )

                data Code = Int
                    invariant atLeastOne = value >= 1
                """));
        ReadableModule read = assertInstanceOf(ReadableModule.class,
                assertInstanceOf(Readback.Ready.class,
                        ModuleReadback.read("lib.rule",
                                ((souther.compiler.meta.ModulePath) classes::get).declarations(), DefaultStdlib.get().names()),
                        "the module was published and is on the path").value());

        List<SourcePos> positions = new ArrayList<>();
        clausesOf(read.module(), positions);

        assertFalse(positions.isEmpty(), "the published module has a clause to have positions in");
        assertEquals(List.of(), positions.stream().filter(p -> !(p.quotedFrom() instanceof QuotedFrom.TextItCannotShow)).toList(),
                "a clause read back is written where this compile has no file");
    }

    /** A file this compile holds is the ordinary case, and nothing about it stands in for anything. */
    @Test
    void everyPositionOfAFileThisCompileHoldsIsAtItsPlace() {
        List<SourcePos> positions = new ArrayList<>();
        Ast.Module module = CstFrontend.parseWithSlices("""
                module app.own

                data Code = Int
                    invariant atLeastOne = value >= 1
                """, null, new SourceId("0")).module();
        clausesOf(module, positions);

        assertFalse(positions.isEmpty(), "the clause has positions");
        assertEquals(List.of(), positions.stream().filter(SourcePos::wasCopiedHere).toList(),
                "what was read off a file the reader holds is where the code is");
        assertEquals(List.of(), positions.stream().filter(p -> !p.isIn(new SourceId("0"))).toList(),
                "and it says which file");
    }

    /**
     * A text nobody has named is the third state, and it is not the second.
     *
     * <p>Naming no source is what a snippet and a published module have in common, and it is not why
     * either of them is what it is. Reading one off the other is the shortcut this whole change
     * removes, so the state that would make it look right again is pinned rather than left to be
     * rediscovered.
     */
    @Test
    void aTextNobodyHasNamedIsWhereItsCodeIsAllTheSame() {
        List<SourcePos> positions = new ArrayList<>();
        Ast.Module module = CstFrontend.parse("""
                module app.own

                data Code = Int
                    invariant atLeastOne = value >= 1
                """);
        clausesOf(module, positions);

        assertFalse(positions.isEmpty(), "the clause has positions");
        assertEquals(List.of(), positions.stream().filter(SourcePos::wasCopiedHere).toList(),
                "somebody wrote this text; what is missing is a name for it, not an author");
        assertEquals(List.of(), positions.stream().filter(p -> p.quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds).toList(),
                "and nothing here has named it");
    }

    // --- and the two questions stay apart -------------------------------------------------------

    /**
     * The witness that neither answer may be read off the other: a library body spliced into a
     * caller is out of sight and in a file this compile holds, at once.
     *
     * <p>Read on one compile so that the two claims are about the same positions. Measured
     * separately, a body that was neither would satisfy each of them by way of a different node.
     */
    @Test
    void aSplicedBodyIsOutOfSightAndInAFileThisCompileHolds() {
        List<SourcePos> positions = new ArrayList<>();
        collect(bodyOf("""
                module demo

                let sized (n: Int): Int = Int.abs(n)
                """, "sized"), positions);

        List<SourcePos> copied = positions.stream().filter(SourcePos::wasCopiedHere).toList();
        assertFalse(copied.isEmpty(), "the body calls into the library, so some of it was copied");
        assertEquals(List.of(), copied.stream().filter(p -> !(p.quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds)).toList(),
                "a copy is read against the caller's file and says which file that is");
    }

    /**
     * The splice replaces the name and nothing else.
     *
     * <p>Where the code is written does not change with how a caller spells its way in, and neither
     * does what kind of thing this compile is without. Held as one string the refinement overwrites
     * the module — {@code souther.int} becomes {@code Int.abs} — and finding the module again would
     * mean splitting a spelling, which is provenance inferred from how a name is written.
     */
    @Test
    void theSpliceRefinesTheNameAndKeepsWhatTheCodeCameFrom() {
        List<SourcePos> positions = new ArrayList<>();
        collect(bodyOf("""
                module demo

                let sized (n: Int): Int = Int.abs(n)
                """, "sized"), positions);

        List<String> said = positions.stream().filter(SourcePos::wasCopiedHere)
                .map(p -> p.placement().toString()).distinct().toList();
        assertTrue(said.stream().allMatch(s -> s.contains("TheStandardLibrary")),
                () -> "the library is still what the copy came from: " + said);
        assertTrue(said.stream().allMatch(s -> s.contains("Int.abs")),
                () -> "under the name the call reaches it by: " + said);
        assertTrue(said.stream().allMatch(s -> s.contains("souther.int")),
                () -> "and the module the parse knew is still there to be read: " + said);
    }

    // --- the fixtures ---------------------------------------------------------------------------

    /** {@code fn}'s body as a check downstream reads it, with every helper call expanded. */
    private static Hir.Expr bodyOf(String source, String fn) {
        var parsed = CstFrontend.parseWithSlices(source, null, new SourceId("demo.sou"));
        Hir.Module module = Resolve.module(parsed.module(), SyntaxSymbols.of(parsed.module(), DefaultStdlib.get()));
        HelperInliner inliner = HelperInliner.forModule(module, DefaultStdlib.get());
        Hir.FnDef body = inliner.held().get(fn);
        assertNotNull(body, "the fn under test is one of the module's own");
        return inliner.inline(body.writtenBody(), inliner.bodyOf(fn));
    }

    /** Where each invariant clause of {@code module} was read, and where the names it declares
     *  were — the positions the parse made, before any pass has rebuilt one. */
    private static void clausesOf(Ast.Module module, List<SourcePos> into) {
        for (Ast.Def def : module.defs()) {
            into.add(def.written().pos());
            if (def instanceof Ast.Data data) {
                data.invariants().forEach(clause -> into.add(clause.pos()));
            }
        }
    }

    private static void collect(Hir.Expr e, List<SourcePos> into) {
        if (e == null) {
            return;
        }
        if (e.pos() != null) {
            into.add(e.pos());
        }
        Hir.forEachChild(e, child -> collect(child, into));
    }
}
