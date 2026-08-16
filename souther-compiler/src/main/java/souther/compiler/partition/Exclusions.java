package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The input classes a behavior's body says it does not answer for.
 *
 * <p>A case a row cannot be written at. Reaching an {@code unreachable} is E1911, so a case whose
 * every path aborts is one no row may name — and a measure that counts it asks for a row the compiler
 * would refuse, which is how a model that states where its combinations cannot arise ends up
 * reporting a coverage it can never reach.
 *
 * <p><b>Only what can be read off the body without deciding anything.</b> The body is followed down
 * its spine — what a {@code let} binds — to the first fork. Where that fork is a {@code match} on an
 * input position, the cases whose arms answer nothing are excluded. A function written where a call
 * takes one is not entered: evaluating that position makes the function, and what it matches on when
 * the call applies it is about its own parameters. Nothing
 * below a fork is read: an arm of one {@code match} holding a {@code match} on another parameter says
 * what that parameter cannot be <em>given the first one</em>, which is not a fact about the parameter
 * and not something a class of it can carry. Nothing is read off a condition either: telling which
 * values satisfy {@code somePredicate(f)} is what a solver does, and a wrong answer here takes away a
 * case the author should have been asked for.
 *
 * <p>So this misses exclusions that hold. That direction is the safe one: a case left in is a case the
 * report asks for, and an author reading a gap they cannot fill is at least told something true about
 * their model — an author never told about a gap is not.
 */
public final class Exclusions {

    /** Nothing excluded: a behavior with no body, or one whose body says nothing this can read. */
    public static final Exclusions NONE = new Exclusions(Map.of());

    private final Map<TermPath, Map<TypeSymbol, List<String>>> byPath;

    private Exclusions(Map<TermPath, Map<TypeSymbol, List<String>>> byPath) {
        this.byPath = byPath;
    }

    /**
     * What {@code body} says it does not answer for.
     *
     * @param parameters the behavior's parameter names, which is what tells a {@code match} on an
     *                   input from a {@code match} on anything else
     */
    public static Exclusions of(Core body, List<String> parameters, Symbols symbols) {
        if (body == null) {
            return NONE;
        }
        if (!(spine(body) instanceof Core.Match match)) {
            return NONE;
        }
        TermPath path = GuardThresholds.pathOf(match.scrutinee(), parameters, symbols);
        if (path == null) {
            return NONE;
        }
        Map<TypeSymbol, List<String>> excluded = new LinkedHashMap<>();
        for (Core.Case arm : match.cases()) {
            if (NormalReturn.of(arm.body())) {
                continue;
            }
            List<String> why = UnreachableReasons.of(arm.body());
            // Cases written together on one arm are one run of code, and it answers nothing for every
            // one of them.
            arm.caseTypes().forEach(each -> excluded.put(each, why));
        }
        return excluded.isEmpty() ? NONE : new Exclusions(Map.of(path, excluded));
    }

    public boolean isEmpty() {
        return byPath.isEmpty();
    }

    /** The cases excluded at one input position, in the order the body rules them out. */
    public List<TypeSymbol> at(TermPath path) {
        return List.copyOf(byPath.getOrDefault(path, Map.of()).keySet());
    }

    /** The cases excluded at a bare parameter, which is what the signature's own measure asks about:
     * it counts a position's cases and knows nothing of the fields inside one. */
    public List<TypeSymbol> atParameter(String name) {
        return at(TermPath.of(name));
    }

    /**
     * Why a case is excluded, as the model wrote it.
     *
     * <p>Every reason on the paths that abort, and not the first one found: an arm made of a
     * {@code match} whose arms abort for different reasons has no single reason, and taking the one
     * written above the others would name it by where it happens to sit in the file.
     */
    public List<String> reasonsFor(TermPath path, TypeSymbol each) {
        return byPath.getOrDefault(path, Map.of()).getOrDefault(each, List.of());
    }

    /**
     * What a body answers with, with the bindings around it removed.
     *
     * <p>Only what is evaluated on the way to the answer is stepped over. Nothing here enters a fork,
     * and nothing enters a {@code Core.Block} either: a block is a function value, and what it
     * matches on when something calls it is about its own parameters rather than about this
     * behavior's inputs.
     */
    private static Core spine(Core body) {
        Core at = body;
        while (at instanceof Core.LetIn let) {
            at = let.body();
        }
        return at;
    }
}
