package souther.compiler.inputs;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which of a body's names stand for a position of its input, where the reader has got to.
 *
 * <p>A reader of a body meets a position under whatever name is in scope there, and the name is not
 * the position. Two things make that so, and one value carries both.
 *
 * <p>A body may bind a name its own behavior already binds. {@code let order = withDefaults(order)}
 * leaves every read below it naming the local, whose values are whatever the call answers with — so
 * a reader matching the word says about the parameter's rules what is true of nothing.
 *
 * <p>And a body reaches a position through the names bound on the way to it. A helper expanded into
 * a body binds the call's argument to the helper's own parameter and matches that, so a reader that
 * followed no binding would find every statement inside an expanded helper about a position it
 * cannot name — which is most of what a model's rules are written in.
 *
 * <p>So a reader descends with the bindings it has passed, and asks this. Nothing here decides what
 * a position holds; that is the reading of the declarations ({@link InputDomain}), and this only
 * says which position a name is pointing at.
 */
public record InputReads(InputDomain read, Map<BindingId, Core> bound) {

    public InputReads {
        bound = Map.copyOf(bound);
    }

    /** At the top of a body, where nothing has been bound yet. */
    public static InputReads of(InputDomain read) {
        return new InputReads(read, Map.of());
    }

    /** The same, inside what {@code binder} binds. */
    public InputReads and(Hir.Binder binder, Core value) {
        if (binder == null || binder.binding() == null || value == null) {
            return this;
        }
        Map<BindingId, Core> wider = new LinkedHashMap<>(bound);
        // The nearest binding wins, which is what being inside it means.
        wider.put(binder.binding(), value);
        return new InputReads(read, wider);
    }

    /** The position {@code e} names here, or null where it names none. */
    public TermPath pathOf(Core e, Symbols symbols) {
        return InputPath.of(e, read, bound, symbols);
    }
}
