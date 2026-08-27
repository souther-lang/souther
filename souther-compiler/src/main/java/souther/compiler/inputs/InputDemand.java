package souther.compiler.inputs;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The finite input paths one behavior's measurement is going to name.
 *
 * <p><b>Named, and nothing more.</b> Nothing here says a value stands at one of these, that a row
 * can be written there, or that the rules leave the case on the way to it anything. It says that the
 * body reads that location, so a reading of the input that could not answer about it would be a
 * reading with nothing to say about a rule the author wrote.
 *
 * <p><b>Which is what lets a reading be built over it.</b> Enumerating what positions a type can
 * have stops where a path returns to a declaration already open on it, because that question has no
 * other end; a demand has an end of its own — the path is as long as the body wrote it. So the
 * reading is built once, over what the enumeration found and what the demand named, and never grows
 * afterwards. Asked the other way round — a reading that resolved a path when somebody looked one up
 * — what a report said would depend on what had been asked before it.
 *
 * <p><b>Over-approximating is allowed and concluding is not.</b> A path here may reach a case the
 * rules refuse or a place the language reads nothing at; the reading answers that when it is asked,
 * and answers it the same way it answers about any other path. What must never happen is the
 * reverse — a path the body names that nothing offered to the reading, which is a rule measured
 * nowhere and reported as a model that states nothing.
 *
 * <p>Read off the locations the tree names rather than off the rules written over them. A threshold,
 * a value singled out, a line between two positions and a claim about a case are all written over
 * expressions the body already reads, so a rule form added later names no location this did not
 * already see — which is the difference between this and a list assembled from the rule kinds there
 * happen to be today.
 */
public record InputDemand(List<TermPath> paths) {

    /** A behavior whose measurement names nothing beyond what the enumeration finds. */
    public static final InputDemand NONE = new InputDemand(List.of());

    /**
     * <p>A list and not a set, kept in the order the paths were met. What order the reading walks
     * its demands in decides the order the positions come out in, which a report prints and a
     * measure counts against — and an immutable set iterates in an order that is not the order
     * anything put things into it. Deduplicated on the way in, so a list is what a set would have
     * been with an order that is somebody's.
     */
    public InputDemand {
        paths = List.copyOf(paths);
    }

    /** The paths at or under {@code parameter}, which is what one parameter's reading is given. */
    public List<TermPath> under(TermPath parameter) {
        List<TermPath> out = new java.util.ArrayList<>();
        for (TermPath each : paths) {
            if (each.isAtOrUnder(parameter)) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /**
     * Every location {@code body} names, read under the bindings on the way to each of them.
     *
     * <p>The environment is the one every reader of a body carries, moved along by the two things
     * that change what a name means: a binding, and an arm that says which case the value it matched
     * turned out to be. Everything else is walked with the environment it stands in.
     *
     * <p>Taken as {@link InputPaths} and not as the reader that implements it, so that the reading
     * of the input is not reachable from here at all. It is the thing being built.
     */
    public static InputDemand of(Core body, InputPaths names, Symbols symbols) {
        if (body == null) {
            return NONE;
        }
        Set<TermPath> found = new LinkedHashSet<>();
        walk(body, names, symbols, found);
        return new InputDemand(List.copyOf(found));
    }

    private static void walk(Core e, InputPaths names, Symbols symbols, Set<TermPath> found) {
        TermPath at = names.pathOf(e, symbols);
        if (at != null) {
            found.add(at);
        }
        switch (e) {
            // The body of a `let` is where the name stands for what was bound to it.
            case Core.LetIn let -> {
                walk(let.value(), names, symbols, found);
                walk(let.body(), names.and(let.binder(), let.value()), symbols, found);
            }
            // And each arm under what the arm says the value it matched turned out to be, which is
            // the one step of a path no expression writes down.
            case Core.Match match -> {
                walk(match.scrutinee(), names, symbols, found);
                for (Core.Case arm : match.cases()) {
                    walk(arm.body(), names.insideArm(match, arm, symbols), symbols, found);
                }
            }
            default -> Core.forEachChild(e, child -> walk(child, names, symbols, found));
        }
    }

    /** The same demand with {@code more} named as well, for a caller that has paths of its own. */
    public InputDemand and(List<TermPath> more) {
        if (more.isEmpty()) {
            return this;
        }
        Set<TermPath> wider = new LinkedHashSet<>(paths);
        wider.addAll(more);
        return new InputDemand(List.copyOf(wider));
    }
}
