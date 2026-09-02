package souther.compiler.query;

import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.ResolvedSymbols;

/**
 * A scope, for a test standing where a compute stands.
 *
 * <p>Here and not on {@link Names} because of what a scope is. It reads declarations by asking the
 * store, so it is a way of asking rather than an answer, and what keeps that honest is that one is
 * built inside the {@code compute} that reads it and goes no further — a public way of getting one
 * is a way of keeping one, which is what {@code Compilation.symbols} was and why it is gone.
 *
 * <p>A test is not a compute and does not have to be. What it may not do is make the production API
 * wider than the rule allows so that it can reach one; so it reaches over the package boundary from
 * inside the package, which is a thing only a test source can do.
 */
public final class Scopes {

    private Scopes() {}

    /** What names mean in {@code module}, over the declarations as they were derived. */
    public static Answer<DerivedSymbols> derived(Db db, String module) {
        return Names.derivedSymbols(db, module);
    }

    /** The same, over the declarations as resolution left them. */
    public static Answer<ResolvedSymbols> resolved(Db db, String module) {
        return Names.resolvedSymbols(db, module);
    }
}
