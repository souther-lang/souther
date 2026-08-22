package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;

import java.util.List;

/**
 * The Core binder a resolved binder is read as.
 *
 * <p>The one place the two forms meet. Core has a binder of its own — a binding and what to call the
 * local — because a backend outside this compiler reads Core, and the resolved binder carries the
 * spelling and place an author wrote, which is the frontend's answer and not a fact about the
 * program being emitted. So the reading is here, in the compiler that owns both forms, rather than
 * on either of them: Core naming the resolved tree is what this removes, and the resolved tree
 * naming Core would only turn the dependency around.
 */
public final class CoreBinders {

    private CoreBinders() {}

    /** The binder {@code binder} is, for Core. Null for the arm of a {@code match} that binds
     *  nothing, which is how that arm carries no binding. */
    public static Core.Binder of(Hir.Binder binder) {
        return binder == null ? null : new Core.Binder(binder.name(), binder.binding());
    }

    /** The same, for a form that binds several at once: a block's parameters. */
    public static List<Core.Binder> all(List<Hir.Binder> binders) {
        return binders.stream().map(CoreBinders::of).toList();
    }
}
