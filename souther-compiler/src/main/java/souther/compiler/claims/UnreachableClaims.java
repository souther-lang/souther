package souther.compiler.claims;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.inputs.InputPath;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * What a behavior's body declares cannot arrive.
 *
 * <p>Claims and nothing else. Reaching an {@code unreachable} is E1911, so a case behind one is a
 * case an author is being told not to write a row at — and what settles whether they should be told
 * that is the model's own rules, not the sentence saying so. Read here, judged in {@link Claims}.
 *
 * <p><b>Only what can be read off the body without deciding anything.</b> The body is followed down
 * its spine — what a {@code let} binds — to the first fork. Where that fork is a {@code match} on an
 * input position, the cases whose arms answer nothing are the ones claimed. A function written where
 * a call takes one is not entered: evaluating that position makes the function, and what it matches
 * on when the call applies it is about its own parameters. Nothing below a fork is read: an arm of
 * one {@code match} holding a {@code match} on another parameter says what that parameter cannot be
 * <em>given the first one</em>, which is not a fact about the parameter and not something a class of
 * it can carry. Nothing is read off a condition either: telling which values satisfy
 * {@code somePredicate(f)} is what a solver does.
 *
 * <p>So claims are missed. That direction is the safe one now that a claim no longer moves a
 * denominator: a claim nothing read is a case the report asks for a row at, and an author reading a
 * gap they cannot fill is at least told something true about their model. What is not safe is the
 * other direction, and it is why this is read apart from what is done with it.
 */
public final class UnreachableClaims {

    /** Nothing claimed: a behavior with no body, or one whose body says nothing this can read. */
    public static final UnreachableClaims NONE = new UnreachableClaims(List.of());

    private final List<Claim> claims;

    private UnreachableClaims(List<Claim> claims) {
        this.claims = List.copyOf(claims);
    }

    /**
     * What {@code body} declares cannot arrive.
     *
     * @param parameters the behavior's parameter names, which is what tells a {@code match} on an
     *                   input from a {@code match} on anything else
     */
    public static UnreachableClaims of(Core body, List<String> parameters, Symbols symbols) {
        if (body == null || !(spine(body) instanceof Core.Match match)) {
            return NONE;
        }
        TermPath path = InputPath.of(match.scrutinee(), parameters, symbols);
        if (path == null) {
            return NONE;
        }
        List<Claim> found = new ArrayList<>();
        for (Core.Case arm : match.cases()) {
            if (NormalReturn.of(arm.body())) {
                continue;
            }
            List<UnreachableReasons.Said> said = UnreachableReasons.said(arm.body());
            List<String> why = said.stream().map(UnreachableReasons.Said::reason).distinct().toList();
            // Cases written together on one arm are one run of code, and it declares the same thing
            // about every one of them.
            arm.caseTypes().forEach(each -> found.add(new Claim(path, each, why,
                    said.isEmpty() ? null : said.get(0).at())));
        }
        return found.isEmpty() ? NONE : new UnreachableClaims(found);
    }

    public boolean isEmpty() {
        return claims.isEmpty();
    }

    /** Every claim, in the order the body makes them. */
    public List<Claim> all() {
        return claims;
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
