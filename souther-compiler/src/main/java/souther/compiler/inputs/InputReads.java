package souther.compiler.inputs;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * What a tree's names stand for, in terms of a behavior's input, where the reader has got to.
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
 * <p>And a name stands for more than a position or nothing. It is a position, or the expression it
 * was given, or an element an operation handed out, or something this knows nothing about
 * ({@link ReadMeaning}). Answered as a position and nothing, the last three were one answer, and a
 * rule written over a name given arithmetic over positions was read as no rule at all.
 *
 * <p>Nothing here decides what a position holds; that is the reading of the declarations
 * ({@link InputDomain}), and this only says what a name is pointing at.
 *
 * @param roots      which bindings name which parameter, in the tree being walked
 * @param callsStand whether an operation the language defines the meaning of is left standing in
 *                   this tree. It is in the representation a declaration's own rules are read in
 *                   and it is not in the one that runs, and the difference is not a detail of the
 *                   walk: a call left standing names no location, which is an answer where such a
 *                   tree is what was handed over and a bug in the caller where it is not
 */
public record InputReads(InputDomain read, Map<BindingId, String> roots,
                         Map<BindingId, Core> bound,
                         souther.compiler.check.ElementBindings elements, boolean callsStand) {

    public InputReads {
        roots = Map.copyOf(roots);
        bound = Map.copyOf(bound);
    }

    /** At the top of a body, where nothing has been bound yet and no element has been handed out. */
    public static InputReads of(InputDomain read) {
        return of(read, souther.compiler.check.ElementBindings.NONE);
    }

    /**
     * The same, of a body whose operations handed their closures the contents of containers.
     *
     * <p>Read where those operations still stood and carried here, since the tree this walks has
     * none of them left in it. A reading given nothing finds every name inside a closure naming no
     * position, which is what it did before there was anything to give.
     */
    public static InputReads of(InputDomain read, souther.compiler.check.ElementBindings elements) {
        return new InputReads(read, read.parameterReads(), Map.of(), elements, false);
    }

    /**
     * At the top of a rule the behavior itself declares, which meets the parameters under the
     * bindings the declaration gave them rather than the ones an implementation did.
     *
     * <p>Which is why this takes them rather than reading them off {@code read}: a behavior nothing
     * implements binds its parameters nowhere a body could, and its clauses still name them.
     */
    public static InputReads ofWhatIsDeclared(InputDomain read, Map<BindingId, String> roots) {
        return new InputReads(read, roots, Map.of(),
                souther.compiler.check.ElementBindings.NONE, true);
    }

    /** The same, inside what {@code binder} binds. */
    public InputReads and(Core.Binder binder, Core value) {
        if (binder == null || binder.binding() == null || value == null) {
            return this;
        }
        Map<BindingId, Core> wider = new LinkedHashMap<>(bound);
        // The nearest binding wins, which is what being inside it means.
        wider.put(binder.binding(), value);
        return new InputReads(read, roots, wider, elements, callsStand);
    }

    /** The position {@code e} names here, or null where it names none. */
    public TermPath pathOf(Core e, Symbols symbols) {
        return InputPath.of(e, roots, bound, elements, symbols, callsStand);
    }

    /**
     * What {@code read}'s name stands for here ({@link ReadMeaning}).
     *
     * <p>The one place a name is given a meaning for this side, and the whole of what this reading
     * knows about one. Every reader that meets a name asks here — the arithmetic that finds the line
     * a rule draws, and the walk that says which positions a rule mentions — so the two agree about
     * what a name is rather than each working out what a missing position meant.
     *
     * <p>A position first, wherever there is one. A name an operation handed an element on is a
     * position where the container is at one, and only where it is not does what the binding holds
     * matter — which is the order the position walk already reads them in, said here so a caller
     * does not have to know it.
     *
     * <p>What it holds is answered last and only as the expression. Whether that expression may
     * stand where the name does is the caller's question, asked of the fact rather than of a
     * permission recorded here: an arithmetic reader substitutes it, and a reader collecting
     * positions walks into it, and neither is the other's rule.
     */
    public ReadMeaning meaningOf(Core.Read read, Symbols symbols) {
        TermPath path = pathOf(read, symbols);
        if (path != null) {
            return new ReadMeaning.Position(path);
        }
        if (elements.containerOf(read.binding()) != null) {
            return new ReadMeaning.Element();
        }
        Core held = bound.get(read.binding());
        // Read in this environment. Bindings are added on the way down and each tells itself from
        // every other, so what was bound after this name does not answer for what it holds — which
        // is why the environment at the binder and the one at the read cannot be told apart yet.
        // Said once here rather than by each reader, so the day they can be, one place changes.
        return held == null || held == read ? new ReadMeaning.Unknown()
                : new ReadMeaning.Through(held, this);
    }

    /** The position an element handed to {@code binding} stands at, or null where it stands at
     *  none ({@link InputPath#elementAt}). */
    public TermPath elementAt(BindingId binding, Symbols symbols) {
        return InputPath.elementAt(binding, roots, bound, elements, symbols, callsStand);
    }

    /** The position {@code e}'s value came from, or null where it came from none. Not where it is:
     *  a value made from a position is not that position ({@link InputPath#cameFrom}). */
    public TermPath cameFrom(Core e, Symbols symbols) {
        return InputPath.cameFrom(e, roots, bound, elements, symbols, callsStand);
    }
}
