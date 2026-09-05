package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

/**
 * The one place a clause is typed below the check that answers for the program, and the one place
 * that says what such a reading may stop on.
 *
 * <p>Two readings type a clause here — a declaration's invariant over its fields, and a behavior's
 * rule over its signature — and both used to catch whatever came out of the elaborator and read it
 * as this analysis meeting its limit. What came out included a representation refusing to be built,
 * so a node saying it had come apart and a shape this reading has no rule for arrived alike, and the
 * compile went on with the invariant quietly undischarged.
 *
 * <p>So the limits are named here and everything else goes past. What this reading may stop on is a
 * call its expansion left standing that it has no signature for, and a clause the elaborator refused
 * — and refusing a clause is what the authoritative check does with a program, not something this
 * reading found out. Nothing else is a limit: an {@code IllegalStateException} from a walk, a node's
 * own refusal, a name read through nothing are this compiler disagreeing with itself, and there is no
 * reading of the program under which they are acceptable.
 */
final class SecondaryClauseReading {

    private SecondaryClauseReading() {}

    /**
     * {@code read} as this reading types it, or the limit it stopped on.
     *
     * <p>{@code standing} is the expansion's own answer about the tree in hand. Asked before the
     * elaborator, because a call left standing that this reading cannot name is a limit and the
     * elaborator has no way to say so: reaching it with one is this compiler having failed to expand
     * what it says it expands, which is what it refuses.
     */
    static TypedClause of(Hir.Expr read, CallsLeftStanding standing, Scope scope, CheckContext ctx,
                          String describing) {
        WhatTheCheckCannotRead unreadable = standingCallNothingHereNames(read, standing, scope);
        if (unreadable != null) {
            InvariantChecker.gaveUp(describing, unreadable);
            return new TypedClause.Stopped();
        }
        try {
            return new TypedClause.Typed(Elaborator.elaborate(read, scope, ctx, Type.BOOL));
        } catch (CompileException why) {
            InvariantChecker.gaveUp(describing,
                    WhatTheCheckCannotRead.secondaryTypingDidNotFinish(why));
            return new TypedClause.Stopped();
        } catch (Unanswerable why) {
            InvariantChecker.gaveUp(describing,
                    WhatTheCheckCannotRead.secondaryTypingDidNotFinish(why));
            return new TypedClause.Stopped();
        }
    }

    /**
     * The first call in {@code read} that {@code standing} says was left there and {@code scope} has
     * no signature for, and null where there is none.
     *
     * <p>Both halves. A call standing in a tree no expansion named is not answered here — it goes on
     * to the elaborator, which says what it is. And a standing call this reading can name is read
     * like any other, which is what a rule scope does with a recursive helper it reaches
     * ({@link Scope#reaching}).
     */
    private static WhatTheCheckCannotRead standingCallNothingHereNames(
            Hir.Expr read, CallsLeftStanding standing, Scope scope) {
        if (read instanceof Hir.Apply call
                && call.answered() instanceof Hir.Var.Denoting callee
                && callee.denotes() instanceof ValueName.Helper) {
            ReachName.Declaration reaches = callee.reachesADeclaration();
            if (standing.names(reaches) && scope.of(callee.denotes(), callee.reaches()) == null) {
                return WhatTheCheckCannotRead.standingCallHasNoSignatureHere(
                        call.written(), call.pos());
            }
        }
        WhatTheCheckCannotRead[] found = {null};
        Hir.forEachChild(read, child -> {
            if (found[0] == null) {
                found[0] = standingCallNothingHereNames(child, standing, scope);
            }
        });
        return found[0];
    }
}
