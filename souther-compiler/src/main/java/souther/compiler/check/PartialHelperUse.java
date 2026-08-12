package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.DiagnosticCode;

import java.util.List;
import java.util.Optional;

/**
 * Checks the two rules that make {@code partial} mean something outside the recursion it is written on
 * (spec §fn-rules).
 *
 * <p>A {@code partial} declaration does not carry Souther's termination guarantee. It does not say the
 * helper diverges — a recursion the analysis cannot prove is written this way too — it says the
 * compiler is not answering for this one. A helper written without it does carry the guarantee, and
 * carries it for everything it reaches, which is what the first rule below enforces: an unmarked helper
 * may not reach a marked one. Without it the guarantee holds only inside a recursion's own
 * strongly-connected group, and a certified helper that calls a {@code partial} one off the group does
 * not terminate.
 *
 * <p>The second rule keeps the first from being walked around. A function type says nothing about
 * termination, so a {@code partial} helper written where a value goes leaves the call graph and arrives
 * somewhere the walk cannot see it. It may be applied; it may not be named. Colouring the function type
 * instead would say it precisely, and is not done: the reach is every higher-order signature, the
 * subtyping between them and what a jar carries of them, for a hole the corpus closes by not writing
 * the name.
 *
 * <p>A behavior's implementing {@code let} is not a helper — {@link HelperInliner#helpersOf} is what
 * says so — and publishes no termination guarantee, so neither rule about reaching applies to it: it
 * may call a {@code partial} helper. That is not a boundary the walk stops at, it is a declaration the
 * walk is never asked about. A helper between the behavior and the {@code partial} one is still a
 * helper and still needs the word.
 *
 * <p>Both rules are about a declaration this module wrote, and each says so itself rather than leaving
 * it to whoever loops. A module emits the recursive helpers it reaches as its own methods, so its fns
 * hold declarations of other modules under names of the same shape; those were answered for where they
 * were written (ADR-0098), and a report about one here would name a definition this module's author
 * never wrote. The two rules are one guarantee seen twice — the first refuses a way around the call
 * graph, the second refuses a way out of it — so a scope on one and not the other is the guarantee
 * holding on one side only.
 */
final class PartialHelperUse {

    private PartialHelperUse() {}

    /** The first rule, for one helper of {@code module}: unmarked, it may reach no {@code partial} one.
     * Asked per helper so that a module with several of them reports all of them in one build — the
     * word goes on each. */
    static void rejectReachingPartial(Ast.FnDef helper, String module,
                                      PartialReachability reachability) {
        if (!helper.declaredBy(module) || helper.partial()) {
            return;
        }
        Optional<List<String>> path = reachability.fromHelper(helper.name());
        if (path.isPresent()) {
            throw reachesPartial(helper, path.get());
        }
    }

    /**
     * The rejection for an unmarked helper that reaches a {@code partial} one, said at the helper's own
     * name and naming the path. One per helper: a helper reaching two of them is one thing to fix, and
     * each member of a mutually-recursive group is reported on its own — the word goes on each of them,
     * so a single report for the group would leave the rest to be found one build at a time.
     */
    private static CompileException reachesPartial(Ast.FnDef helper, List<String> path) {
        String reached = path.get(path.size() - 1);
        String rendered = PartialReachability.render(path);
        return CompileException.of(Diagnostic
                        .at(helper.written().reportedAt()).say(new BehaviorMessage.ItReachesAPartialHelper(helper.name(), reached, rendered)).build());
    }

    /**
     * The second rule, for one fn of {@code module}: it may write no {@code partial} helper where a
     * value goes.
     *
     * <p>Asked of every fn and not only of the helpers. A behavior's implementing {@code let} may call
     * a {@code partial} helper and may not hand it over either — what the rule is about is the function
     * value, which is the same thing wherever it is written.
     */
    static void rejectNamedAsValue(Ast.FnDef fn, String module, PartialReachability reachability) {
        if (!fn.declaredBy(module) || !(fn.body() instanceof Ast.FnBody.Written written)) {
            return;
        }
        walkForNamedAsValue(written.expr(), reachability);
    }

    /**
     * Walks {@code e} for a {@code partial} helper written where a value goes. The callee of an
     * application is not such a place — that is the call the rule allows — so it is skipped where it is
     * a name and walked where it is anything else.
     */
    private static void walkForNamedAsValue(Ast.Expr e, PartialReachability reachability) {
        switch (e) {
            case Ast.Apply call -> {
                if (!(call.function() instanceof Ast.Var)) {
                    walkForNamedAsValue(call.function(), reachability);
                }
                for (Ast.Expr arg : call.args()) {
                    walkForNamedAsValue(arg, reachability);
                }
            }
            case Ast.Var v -> {
                // A `let` with no parameter list is a value, not a function: reading its name runs its
                // body where it is written, which the reachability walk follows. Only a name standing
                // for a helper that takes arguments becomes a function value, and that is the one a
                // function type would have to carry the guarantee for and cannot.
                if (reachability.isPartialFunctionNamed(v)) {
                    throw CompileException.of(Diagnostic
                                    .at(v.written().reportedAt()).say(new BehaviorMessage.APartialHelperIsWrittenWhereAValueGoes(v.name())).build());
                }
            }
            default -> Ast.forEachChild(e, child -> walkForNamedAsValue(child, reachability));
        }
    }
}
