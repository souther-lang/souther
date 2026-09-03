package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.frontend.CstFrontend;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an author applied and what is applied now are two answers, and the first is not read off the
 * second.
 *
 * <p>The states they differ in are the passes that replace what a call applies, and there are three.
 * A field read applied is bound to a name of its own and the binding applied. A sugared library name
 * becomes the operation it stands for. A helper of another module is written qualified where a
 * reader reaches it. Each is written down here, because a law with no state that tells its two
 * answers apart is a law two accessors could be collapsed under without anything moving.
 *
 * <p>The sugar is the one this began with and is
 * {@link AReportQuotesTheNameTheAuthorAppliedTest}'s, where what a reader is told is the whole
 * question. The other two are here.
 *
 * <p>And the applied answer is itself a pair, for a reason the same shape: a name the author
 * parenthesized is written over fewer characters than it is applied over. Reading the second off
 * the first is what putting them in one value rules out, so a state where they differ is written
 * down too.
 */
class WhatWasAppliedAndWhatIsAppliedAreTwoAnswersTest {

    /**
     * A field read applied: the author applied something that is not a name, and a name is what is
     * applied once the lowering has bound it.
     *
     * <p>Both are names after the lowering, and neither answer is the other's before it. Told apart
     * by the node they are read from and not by which pass has run, which is what a reader holding
     * one of these has to hand.
     */
    @Test
    void aFieldReadAppliedIsANameTheAuthorDidNotApply() {
        Hir.Apply read = theCallIn("""
                module demo

                data Deps = { count: (Int) -> Int }

                behavior go : (d: Deps) -> Int
                let go (d) = d.count(1)
                """);

        assertTrue(read.applied().isAName(), "`d.count` is a name, written as a chain of reads");
        assertEquals("d.count", read.written());
        assertFalse(read.calleeIsAName(), "and a field read is what stands in the callee position");

        Hir.Apply lowered = read.replacedBy(binding("$fn0", read));

        assertTrue(lowered.applied().isAName(), "what was applied is what it was");
        assertEquals("d.count", lowered.written());
        assertTrue(lowered.calleeIsAName(), "and a name is what is applied now");
        assertNotEquals(lowered.written(), lowered.answered().reaches(),
                "the two are not one answer, which is the whole of it");
    }

    /**
     * A name the author parenthesized: written over the name and applied over the parentheses.
     *
     * <p>Both are the reading's, and the second is not the first widened by a rule. What the callee
     * covers is whatever the source put there, and a report about what is applied underlines it.
     */
    @Test
    void aParenthesizedNameIsAppliedOverMoreThanItIsWrittenOver() {
        Hir.Apply read = theCallIn("""
                module demo

                data Deps = { f: (Int) -> Int }

                behavior go : (d: Deps) -> Int
                let go (d) = (d.f)(1)
                """);

        assertEquals("d.f", read.written());
        assertNotEquals(read.applied().name().region(), read.appliedAt(),
                "the parentheses are applied over and are not part of the name");
        assertTrue(souther.compiler.diag.Region.encloses(read.appliedAt(),
                        read.applied().name().region()),
                "and what is applied over takes the name in");

        Hir.Apply lowered = read.replacedBy(binding("$fn0", read));

        assertEquals(read.appliedAt(), lowered.appliedAt(),
                "a rewrite of what is applied moves no characters");
        assertEquals(read.applied().name().region(), lowered.applied().name().region());
    }

    /**
     * A helper of another module, reached by the qualified name a reader writes it under.
     *
     * <p>The author wrote it bare, an import having brought it in, and the pass that settles how a
     * reader reaches it replaces the callee. A recursive one is lowered to a method rather than
     * expanded, so the call is still a call where it is typed — which is where a reader is told
     * about it.
     */
    @Test
    void anImportedHelperIsReportedByTheNameItsCallerWrote() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(SPINNING, """
                        module order exposing ( Receipt, bill )

                        import maths ( spin )

                        data Receipt = { total: Int }

                        behavior bill : (n: Int) -> Receipt constructs Receipt
                        let bill (n) = Receipt { total = spin(n, n) }
                        """)));

        assertFalse(refused.getMessage().contains("maths.spin"),
                () -> "the reader reaches it under that name and its author wrote another: "
                        + refused.getMessage());
        assertTrue(refused.getMessage().contains("`spin`"),
                () -> "which is `spin`: " + refused.getMessage());
    }

    /** And the same where what is wrong is an argument rather than how many there are. */
    @Test
    void andWhereWhatIsWrongIsAnArgumentRatherThanTheirNumber() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(SPINNING, """
                        module order exposing ( Receipt, bill )

                        import maths ( spin )

                        data Receipt = { total: Int }

                        behavior bill : (n: Int) -> Receipt constructs Receipt
                        let bill (n) = Receipt { total = spin("no") }
                        """)));

        assertFalse(refused.getMessage().contains("maths.spin"), refused::getMessage);
        assertTrue(refused.getMessage().contains("of spin"), refused::getMessage);
    }

    private static final String SPINNING = """
            module maths exposing ( spin )

            partial let spin (n: Int) : Int = if n == 0 then 0 else spin(n - 1)
            """;

    /** The one application {@code source} writes, as the reading answered it. */
    private static Hir.Apply theCallIn(String source) {
        Ast.Module parsed = CstFrontend.parse(source);
        List<Hir.Apply> found = new ArrayList<>();
        for (Hir.FnDef fn : Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()))
                .fns()) {
            if (fn.body() instanceof Hir.FnBody.Written written) {
                applicationsIn(written.expr(), found);
            }
        }
        assertEquals(1, found.size(), "this test is about the one application the source writes");
        return found.get(0);
    }

    private static void applicationsIn(Hir.Expr e, List<Hir.Apply> out) {
        if (e instanceof Hir.Apply call) {
            out.add(call);
        }
        TypeChecker.forEachChild(e, child -> applicationsIn(child, out));
    }

    /** A binding a lowering would put in the callee position, standing where the callee stood. */
    private static Hir.Var binding(String name, Hir.Apply call) {
        souther.compiler.types.ValueName.Local local = new souther.compiler.types.ValueName.Local(
                name, new souther.compiler.types.BindingId(
                        new souther.compiler.types.BindingOwner.OfValue("demo", "go"), 0));
        return Hir.Var.respelled(name, new souther.compiler.types.ReachName.InScope(local),
                call.function().pos(), call.function().region());
    }
}
