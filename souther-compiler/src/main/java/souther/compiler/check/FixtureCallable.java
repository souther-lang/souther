package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.check.FixtureApplication.SettledCall;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a settled call's method is, and what has to be emitted for it to be there.
 *
 * <p>Representation and nothing else. Whether the row may apply the call was answered by
 * {@link FixtureApplication}, and a {@link SettledCall} is the evidence — so this asks nothing about
 * type variables, refuses nothing, and takes no call that has not been settled. That is what keeps a
 * fact about the backend from deciding which rows are admitted, which is the shape the standard
 * library's calls were refused by before.
 *
 * <p>A kernel has no method to reach: it is lowered where it is called, so a row applying one is
 * given a body written for it — its own parameters handed to the one call — and that body is
 * lowered like any other. It is written at the instance the row settled rather than at the
 * declaration, because a kernel's lowering may read the type it is applied at: {@code List.sum}
 * chooses between two runtime methods by whether it is summing {@code Int} or {@code Decimal}, and
 * a body written at {@code List<'a>} has nothing for it to choose by.
 */
public final class FixtureCallable {

    private FixtureCallable() {
    }

    /** The name a kernel's method is emitted under. Written nowhere a source could spell, so what is
     *  emitted under it is reached from a fixture and from nothing else. */
    private static final String INTRINSIC_PREFIX = "$intrinsic.";

    /**
     * How a settled call is reached: the method to invoke, and the definition to emit for it, null
     * where the module already emits one.
     */
    public record Realization(String method, Hir.FnDef synthesized) {
    }

    /** Where {@code call}'s method is. */
    public static Realization resolve(SettledCall call) {
        if (!(call.declaration().body() instanceof Hir.FnBody.Intrinsic)) {
            // A helper written in Souther already has a method, and the settled call is reached
            // through it: what a fixture applies is one instance, and what runs it need not be one
            // method per instance. Measured rather than assumed — a Souther body carrying an open
            // variable into a kernel that chooses by type is refused where it is written, so the one
            // method it has never has that choice to make.
            return new Realization(call.reached(), null);
        }
        String method = INTRINSIC_PREFIX + call.reached() + instanceTag(call);
        return new Realization(method, wrapper(call, method));
    }

    /**
     * What tells one instance's method from another's: the signature the call settled, in the
     * declaration's own order. Empty where the declaration had nothing to settle, so a monomorphic
     * kernel keeps the one name it has always had.
     *
     * <p>The signature and not the substitution. Which variable was bound to what is how this
     * instance was arrived at; what it <em>is</em> is the signature that came out, and two calls
     * arriving at one signature are one instance. The readable half is for whoever reads the emitted
     * class; the digest is what makes two signatures that flatten to the same spelling different
     * names.
     */
    private static String instanceTag(SettledCall call) {
        if (!call.instantiated()) {
            return "";
        }
        StringBuilder signature = new StringBuilder();
        for (Type p : call.params()) {
            signature.append(Type.show(p)).append(',');
        }
        signature.append("->").append(call.result() == null ? "" : Type.show(call.result()));
        String written = signature.toString();
        return "$" + spellable(written) + "$" + Integer.toHexString(written.hashCode());
    }

    /** {@code written} as a name a method may be emitted under: everything a JVM name cannot carry
     *  becomes an underscore, which is why the digest stands beside it. */
    private static String spellable(String written) {
        StringBuilder out = new StringBuilder(written.length());
        for (int i = 0; i < written.length(); i++) {
            char c = written.charAt(i);
            out.append(Character.isLetterOrDigit(c) ? c : '_');
        }
        return out.toString();
    }

    /**
     * {@code call} as a helper with a body: it applies the kernel to its own parameters, at the
     * instance the row settled.
     *
     * <p>What the module could not take on before. A kernel has no body to emit, so nothing was
     * emitted and a row applying one was told a rule about the standard library; the eta-expansion is
     * a body, and the backend lowers the one call in it exactly as it lowers that call anywhere else.
     * So this materialises a method without teaching anything a second way to run a kernel.
     */
    private static Hir.FnDef wrapper(SettledCall call, String method) {
        Hir.FnDef declaration = call.instantiatedDeclaration();
        List<Hir.Expr> args = new ArrayList<>();
        for (Hir.FnParam p : declaration.params()) {
            args.add(Hir.Var.local(p.binder(), declaration.pos()));
        }
        ValueName.Stdlib target = Prelude.operation(call.reached());
        Hir.Expr body = new Hir.Apply(call.reached(), target, new ReachName.OfLibrary(target), args,
                ConstructionOrigin.own(), declaration.pos(), null);
        return declaration.reachedAs(method).withBody(new Hir.FnBody.Written(body));
    }
}
