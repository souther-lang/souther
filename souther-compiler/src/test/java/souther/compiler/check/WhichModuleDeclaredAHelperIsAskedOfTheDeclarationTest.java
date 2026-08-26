package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which module declared a helper is read off the declaration, never off the name it is reached by.
 *
 * <p>The two used to be one question. A module emits the recursive helpers it reaches as its own
 * methods, under the names it reaches them by, so from that point its fns hold declarations of
 * several modules side by side — and the only thing left saying which was which was the dot the
 * qualified name was joined with. Every rule about the declaring module was then a rule about the
 * spelling: the totality check may only require a descent of what this module wrote (ADR-0098), and
 * it asked whether the name had a dot in it.
 *
 * <p>No source can spell the two apart — an identifier holds no dot — so the tables below are built
 * where a table is built rather than compiled from a file. Each is a shape the pipeline produces: a
 * published closure is keyed and named qualified by the module that declares it, and an imported
 * helper arrives under whatever name the reader reaches it by.
 */
class WhichModuleDeclaredAHelperIsAskedOfTheDeclarationTest {

    private static Hir.Module resolved(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        return Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
    }

    /** {@code source} resolved with {@code imported} (bare name -> declaring module) reachable, which
     * is what the query layer hands a module that writes an {@code import}. */
    private static Hir.Module resolved(String source, Map<String, String> imported) {
        Ast.Module parsed = CstFrontend.parse(source);
        Map<String, ValueName.Helper> helpers =
                new LinkedHashMap<>(Resolve.Reachable.of(parsed).helpers());
        imported.forEach((bare, module) -> helpers.put(bare, new ValueName.Helper(module, bare)));
        Resolve.Resolution answered = Resolve.resolving(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()),
                new Resolve.Values(
                        new Resolve.Reachable(parsed.name(), helpers, Map.of(), java.util.Set.of(), true, Map.of(),
                                java.util.Set.of()),
                        Resolve.Elsewhere.NONE));
        if (!answered.unresolved().isEmpty()) {
            throw answered.unresolved().get(0);
        }
        return answered.module();
    }

    /** A module declaring one recursive helper that descends on nothing. */
    private static Hir.FnDef spinOf(String module) {
        Hir.Module m = resolved("module " + module + "\n\nlet spin (n: Int) : Int = spin(n)\n");
        return HelperInliner.helpersOf(m).get("spin");
    }

    /** The totality check over a module that declared {@code declared} and took {@code takenOn} on to
     * emit. Both are walked; only the first is this module's to prove. */
    private static void check(String module, Map<String, Hir.FnDef> declared,
                              Map<String, Hir.FnDef> takenOn) {
        HelperTable table =
                HelperTable.of(module, declared, takenOn, Map.of(), InliningPolicy.FULL, DefaultStdlib.get());
        TotalityChecker.check(HelperInliner.over(table, HelperGraph.of(table)));
    }

    /**
     * A helper `maths` wrote, held at a qualified address — the shape a published body is closed
     * into. Its descent is still `maths`'s to require.
     *
     * <p>The address is not the answer. It is where the module puts the method, and a rule that
     * read the dot in it would skip this one — which is accepting a recursion nobody proved.
     */
    @Test
    void whereItIsHeldIsNotAnExemption() {
        Hir.FnDef own = spinOf("maths");
        HelperInliner maths = HelperInliner.forHelpers("maths", Map.of("spin", own), DefaultStdlib.get());
        Hir.FnDef closed = maths.closeAcross(own, "maths");

        assertEquals("maths.spin", closed.name());
        assertEquals("maths", closed.declaredIn());

        CompileException refused = assertThrows(CompileException.class,
                () -> check("maths", Map.of(), Map.of(closed.name(), closed)));
        assertEquals("E2001", refused.code());
    }

    /**
     * The same definition, held by a module that did not write it. Its descent is not that module's
     * to require: the module that wrote it required it there, and an unmarked published helper
     * answers for its whole closure (ADR-0098).
     *
     * <p>Which is decided by the declaration and by nothing about the address. Both modules hold it
     * at {@code maths.spin} and both reach it the same way — so the address, the reference and the
     * rendering are all the same in the two, and the only thing that differs is who wrote it.
     */
    @Test
    void aDefinitionAnotherModuleWroteIsNotThisOnesToProve() {
        Hir.FnDef own = spinOf("maths");
        HelperInliner maths = HelperInliner.forHelpers("maths", Map.of("spin", own), DefaultStdlib.get());
        Hir.FnDef closed = maths.closeAcross(own, "maths");

        assertEquals("maths", closed.declaredIn());
        assertDoesNotThrow(() -> check("order", Map.of(), Map.of(closed.name(), closed)));
    }

    /**
     * A helper this module took on to emit is a terminal in the {@code partial}-reachability graph:
     * what it reaches is answered by the module that declared it (ADR-0098), so this one does not
     * walk its body.
     *
     * <p>Trust is only visible against something it would otherwise have caught, so {@code wrapped}
     * below is unmarked and reaches a {@code partial} helper — which the module declaring it rejects.
     * That is what a module published under an older boundary version can look like
     * ({@link souther.compiler.codegen.Backend#BOUNDARY_VERSION}), and where the rule says the reader
     * does not re-derive it, the reader must not report it either.
     */
    @Test
    void aHelperTakenOnToEmitIsATerminal() {
        Hir.Module maths = resolved("""
                module maths exposing ( wrapped )

                partial let spin (n: Int) : Int = spin(n)
                let wrapped (n: Int) : Int = spin(n)
                """);
        Map<String, Hir.FnDef> declared = HelperInliner.helpersOf(maths);
        HelperInliner from = HelperInliner.forHelpers("maths", declared, DefaultStdlib.get());
        Hir.FnDef spin = from.closeAcross(declared.get("spin"), "maths");
        Hir.FnDef wrapped = from.closeAcross(declared.get("wrapped"), "maths");

        Hir.Module order = resolved("""
                module order

                import maths ( wrapped, spin )

                let throughWrapped (n: Int) : Int = wrapped(n)
                let straightToSpin (n: Int) : Int = spin(n)
                """, Map.of("wrapped", "maths", "spin", "maths"));
        Map<String, Hir.FnDef> takenOn = new LinkedHashMap<>();
        takenOn.put(spin.name(), spin);
        takenOn.put(wrapped.name(), wrapped);
        HelperTable table = HelperTable.of("order", HelperInliner.helpersOf(order), takenOn,
                Map.of(), InliningPolicy.FULL, DefaultStdlib.get());
        PartialReachability reachability =
                PartialReachability.of(HelperInliner.over(table, HelperGraph.of(table)));

        // `wrapped` is unmarked, and what it reaches is the module that declared it to answer for.
        assertEquals(Optional.empty(),
                reachability.fromHelper(new ReachName.OfModule(
                        new ValueName.Helper("maths", "wrapped"))));
        assertEquals(Optional.empty(),
                reachability.fromHelper(new ReachName.Bare(
                        new ValueName.Helper("order", "throughWrapped"))));
        // The rule stops at the boundary rather than everywhere: a `partial` helper of another
        // module is still one, and what this module wrote is still walked to find it.
        assertEquals(Optional.of(List.of(
                        new ReachName.Bare(new ValueName.Helper("order", "straightToSpin")),
                        new ReachName.OfModule(new ValueName.Helper("maths", "spin")))),
                reachability.fromHelper(new ReachName.Bare(
                        new ValueName.Helper("order", "straightToSpin"))));
    }

    /**
     * The other half of the same guarantee. A {@code partial} helper may not be written where a value
     * goes, which is what keeps it from leaving the call graph the rule above walks — and that rule is
     * about a declaration this module wrote, for the reason the one above is.
     *
     * <p>Asked of every fn rather than of the helpers, since a behavior's own {@code let} may not hand
     * one over either, so the fns of a module are exactly where a declaration it only took on to emit
     * turns up.
     *
     * <p>The body below is the declaration as its own module wrote it, which is the shape a reader
     * meets a library helper in: those come from {@code DefaultStdlib.get().helpers()}, whose bodies were never
     * closed. A body that <em>was</em> closed cannot carry this at all — the expansion eta-expands a
     * helper named where a value goes — so this rule and the one above meet a foreign declaration by
     * different routes and need the same scope either way.
     */
    @Test
    void aHelperTakenOnToEmitIsNotReReadForAPartialHandedOver() {
        Hir.Module maths = resolved("""
                module maths exposing ( hands )

                partial let spin (n: Int) : Int = spin(n)
                partial let loop (f: (Int) -> Int, n: Int) : Int = loop(f, n)
                let hands (n: Int) : Int = loop(spin, n)
                """);
        Map<String, Hir.FnDef> declared = HelperInliner.helpersOf(maths);
        HelperInliner from = HelperInliner.forHelpers("maths", declared, DefaultStdlib.get());
        Hir.FnDef spin = from.closeAcross(declared.get("spin"), "maths");
        Hir.FnDef written = declared.get("hands");
        // Taken on by `order` under the name it reaches it by, and its body read against `order`'s
        // names: a body a reader holds names what the reader reaches, whoever declared it.
        Hir.FnDef hands = written
                .reachedAs(new ReachName.OfModule(new ValueName.Helper("maths", "hands")))
                .withBody(new Hir.FnBody.Written(
                HelperNames.qualifyHelpersOf(written.writtenBody(), "maths")));

        Hir.Module order = resolved("""
                module order

                let ownWork (n: Int) : Int = n + 1
                """);
        Map<String, Hir.FnDef> takenOn = new LinkedHashMap<>();
        takenOn.put(spin.name(), spin);
        takenOn.put(hands.name(), hands);
        HelperTable table = HelperTable.of("order", HelperInliner.helpersOf(order), takenOn,
                Map.of(), InliningPolicy.FULL, DefaultStdlib.get());
        PartialReachability reachability =
                PartialReachability.of(HelperInliner.over(table, HelperGraph.of(table)));

        // `maths` answered for its own body. Reading it again here reports `maths.spin` against a
        // module whose author never wrote it.
        assertDoesNotThrow(() ->
                PartialHelperUse.rejectNamedAsValue(hands, "order", reachability));
        // Where it was written, the same body is the module's own to answer for.
        CompileException refused = assertThrows(CompileException.class,
                () -> PartialHelperUse.rejectNamedAsValue(hands, "maths", reachability));
        assertEquals("E2001", refused.code());
    }

    /**
     * The library's own case, and the reason the name cannot be asked at all: a prelude helper is
     * reached under the library's alias and declared in the module the source says. {@code List} is
     * not {@code souther.list}, so the module a name came from is not in the name — the dot only ever
     * said that there was one.
     */
    @Test
    void theNameAHelperIsReachedByDoesNotHoldTheModuleThatWroteIt() {
        Hir.FnDef foldFrom = DefaultStdlib.get().helpers().get("List.foldFrom");

        assertEquals("souther.list", foldFrom.declaredIn());
        assertTrue(foldFrom.declaredIn().startsWith("souther."));
        assertEquals("souther.list", foldFrom.reachedAs(new ReachName.OfLibrary(
                ValueName.Stdlib.operation("List", "foldFrom"))).declaredIn());
    }
}
