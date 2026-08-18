package souther.compiler.inputs;

import souther.compiler.ast.Hir;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Which of a tree's names stand for a position of a behavior's input, where the reader has got to.
 *
 * <p>A reader meets a position under whatever name is in scope there, and the name is not the
 * position. Three things make that so, and one value carries them.
 *
 * <p>A tree may bind a name the behavior already binds. {@code let order = withDefaults(order)}
 * leaves every read below it naming the local, whose values are whatever the call answers with — so
 * a reader matching the word says about the parameter's rules what is true of nothing.
 *
 * <p>And a body reaches a position through the names bound on the way to it. A helper expanded into
 * a body binds the call's argument to the helper's own parameter and matches that, so a reader that
 * followed no binding would find every statement inside an expanded helper about a position it
 * cannot name — which is most of what a model's rules are written in.
 *
 * <p>And the parameters themselves are bound more than once. An implementation binds them where its
 * body reads them; the declaration binds them where its own {@code ensures} clauses do. Which
 * position a name points at is the same question in either tree, and which bindings ask it is not —
 * so the roots belong to the reading rather than to the input, and a reading given the other one's
 * finds every comparison about nothing.
 *
 * <p>Nothing here decides what a position holds; that is the reading of the declarations
 * ({@link InputDomain}), and this only says which position a name is pointing at.
 *
 * @param roots      which bindings name which parameter, in the tree being walked
 * @param callsStand whether an operation the language defines the meaning of is left standing in
 *                   this tree. It is in the representation a declaration's own rules are read in
 *                   and it is not in the one that runs, and the difference is not a detail of the
 *                   walk: a call left standing names no location, which is an answer where such a
 *                   tree is what was handed over and a bug in the caller where it is not
 */
public record InputReads(InputDomain read, Map<BindingId, String> roots,
                         Map<BindingId, Core> bound, boolean callsStand) {

    public InputReads {
        roots = Map.copyOf(roots);
        bound = Map.copyOf(bound);
    }

    /** At the top of a body, where nothing has been bound yet. */
    public static InputReads of(InputDomain read) {
        return new InputReads(read, read.parameterReads(), Map.of(), false);
    }

    /**
     * At the top of a rule the behavior itself declares, which meets the parameters under the
     * bindings the declaration gave them rather than the ones an implementation did.
     *
     * <p>Which is why this takes them rather than reading them off {@code read}: a behavior nothing
     * implements binds its parameters nowhere a body could, and its clauses still name them.
     */
    public static InputReads ofWhatIsDeclared(InputDomain read, Map<BindingId, String> roots) {
        return new InputReads(read, roots, Map.of(), true);
    }

    /** The same, inside what {@code binder} binds. */
    public InputReads and(Hir.Binder binder, Core value) {
        if (binder == null || binder.binding() == null || value == null) {
            return this;
        }
        Map<BindingId, Core> wider = new LinkedHashMap<>(bound);
        // The nearest binding wins, which is what being inside it means.
        wider.put(binder.binding(), value);
        return new InputReads(read, roots, wider, callsStand);
    }

    /** The position {@code e} names here, or null where it names none. */
    public TermPath pathOf(Core e, Symbols symbols) {
        return InputPath.of(e, roots, bound, symbols, callsStand);
    }
}
