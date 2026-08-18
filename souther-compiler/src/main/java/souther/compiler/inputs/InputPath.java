package souther.compiler.inputs;

import souther.compiler.check.Location;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.Map;

/**
 * Which position of a behavior's input an expression names, or nothing where it names none.
 *
 * <p>One answer, for every reader of a body that has something to say about a position. A
 * {@code guard} comparing a field, a {@code match} on a parameter and an arm declaring a case
 * cannot arrive are three statements about the same positions, and each working out for itself
 * which position it was talking about is three spellings of one path — of which the axes carry one,
 * so the other two would be about positions nothing measures.
 *
 * <p><b>Asked of the binding and never of the spelling.</b> A body may bind a name its own behavior
 * already binds, and the two are different values under one word: {@code let f = defaulted(f)}
 * leaves every read below it naming the local, whose values are whatever the call answers with.
 * Read by name, the reads below it are the parameter's, and what is said about the parameter's rules
 * is said about a value they never reached ({@link BindingId} states this for every reader at once).
 *
 * <p>Nothing about the reading of an input reaches this and nothing here reaches it: what a position
 * can hold is read from the declarations ({@link InputDomain}), and this only says which position an
 * expression is pointing at.
 */
public final class InputPath {

    /**
     * The position {@code e} names.
     *
     * <p>Which fields are steps is {@link Location}'s rule, asked here rather than restated: a
     * newtype's {@code value} is not one, so {@code request.cost} and {@code request.cost.value}
     * are one position, and if the two spellings disagreed the same position would become two axes,
     * one of which no row would ever cover.
     *
     * <p>The root is the parameter as the behavior declares it. What a behavior takes is what it
     * declares, and a declared parameter is not a binding — a behavior with no implementation has
     * positions all the same — so a path is rooted at the declaration and {@link Location} at the
     * binding a body gave it.
     */
    public static TermPath of(Core e, InputDomain read, Symbols symbols) {
        return of(e, read.parameterReads(), Map.of(), symbols, false);
    }

    /**
     * The same, through what a run of {@code let}s bound on the way.
     *
     * <p>A name bound to an input position is that position: what a {@code let} binds is evaluated
     * on the way to the answer, so a body that names its argument and then matches the name is
     * matching the argument. That is what a helper expanded into a body looks like — the call's
     * argument bound to the helper's own parameter — and reading only the outermost name would
     * leave every claim inside an expanded helper about a position nothing here can name.
     *
     * <p>Only through what was bound, and only to a value that is itself a position. A binding whose
     * value is a call is a value the rules of no position say anything about, and it answers
     * nothing here.
     *
     * @param roots      which bindings name which parameter, in the tree being walked
     * @param bound      what each binding on the way holds, in the order they were passed
     * @param callsStand whether this tree is one that keeps the operations the language defines the
     *                   meaning of standing. Where it is, such a call names no location and that is
     *                   the answer; where it is not, meeting one says the walk was handed a
     *                   representation it does not read
     */
    public static TermPath of(Core e, Map<BindingId, String> roots, Map<BindingId, Core> bound,
                              Symbols symbols, boolean callsStand) {
        return of(e, roots, bound, symbols, callsStand, 0);
    }

    private static TermPath of(Core e, Map<BindingId, String> roots, Map<BindingId, Core> bound,
                               Symbols symbols, boolean callsStand, int through) {
        return switch (e) {
            case Core.Read r -> {
                String parameter = roots.get(r.binding());
                if (parameter != null) {
                    yield TermPath.of(parameter);
                }
                Core held = bound.get(r.binding());
                // A binding holds one value, so following it cannot come back to itself; the count
                // is what says so to a reader rather than a claim in a comment.
                yield held == null || through >= bound.size() ? null
                        : of(held, roots, bound, symbols, callsStand, through + 1);
            }
            case Core.FieldAccess fa -> {
                TermPath base = of(fa.target(), roots, bound, symbols, callsStand, through);
                if (base == null) {
                    yield null;
                }
                yield Location.isStep(fa.target().type(), fa.field(), symbols)
                        ? base.then(fa.field()) : base;
            }
            // A call kept standing names no location. Where the walk is over a tree that keeps them
            // that is the answer, and where it is not, its presence says this walk was handed a
            // representation it does not read — said rather than answered with "no path", which
            // would be the same answer a number gives.
            case Core.PreservedCall p -> {
                if (!callsStand) {
                    throw p.unexpectedIn("an input position");
                }
                yield null;
            }
            case null, default -> null;
        };
    }

    private InputPath() {}
}
