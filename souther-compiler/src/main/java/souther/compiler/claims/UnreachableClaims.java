package souther.compiler.claims;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.NormalReturn;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
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
 * <p><b>Every claim the body makes about a position of its input, and the arm it makes it at.</b>
 * A {@code match} on an input position, wherever it is written, has an arm per case, and an arm
 * that answers nothing is that case being declared not to arrive. What is read off each is the
 * same; what differs is whether anything arrives there, and that is not decided here — the claim
 * carries the arm and the reading of what arrives answers about it.
 *
 * <p>Names are resolved through what the {@code let}s in scope bound, so a helper expanded into the
 * body is read against the position the call handed it. A function written where a call takes one is
 * entered like anything else: what it matches on is resolved the same way, and a name it binds
 * itself resolves to no position of this input, which is the answer that arm deserves.
 *
 * <p>Nothing is read off a condition: telling which values satisfy {@code somePredicate(f)} is what
 * a solver does. So claims are missed, and that direction is the safe one now that a claim moves no
 * denominator — a claim nothing read is a case the report asks for a row at, and an author reading a
 * gap they cannot fill is at least told something true about their model.
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
     * @param read the reading of the behavior's input, which is what tells a {@code match} on one
     *             of its positions from a {@code match} on anything else
     */
    public static UnreachableClaims of(Core body, InputDomain read, Symbols symbols,
                                       souther.compiler.coverage.CoverageSites.Plan plan) {
        if (body == null) {
            return NONE;
        }
        List<Claim> found = new ArrayList<>();
        claimedUnder(body, InputReads.of(read), symbols, plan, found);
        return found.isEmpty() ? NONE : new UnreachableClaims(found);
    }

    /**
     * Every claim under {@code e}, each standing behind whatever arm it is written in.
     *
     * <p>One walk over the body. Which fork is the one nothing stands above is settled before it
     * starts and asked by identity here, because that is a fact about where the fork sits and not
     * about what it looks like.
     */
    private static void claimedUnder(Core e, InputReads reads, Symbols symbols,
                                     souther.compiler.coverage.CoverageSites.Plan plan,
                                     List<Claim> found) {
        if (e == null) {
            return;
        }
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        if (e instanceof Core.Match match) {
            claimedIn(match, inside, symbols, plan, found);
        }
        Core.forEachChild(e, child -> claimedUnder(child, inside, symbols, plan, found));
    }

    /**
     * What one {@code match} declares, and the scrutinee it declares it about.
     *
     * <p>Says nothing where the scrutinee names no position of this input: there is nothing to
     * claim about, and what is under its arms is walked by the caller either way.
     */
    private static void claimedIn(Core.Match match, InputReads reads, Symbols symbols,
                                  souther.compiler.coverage.CoverageSites.Plan plan,
                                  List<Claim> found) {
        TermPath path = reads.pathOf(match.scrutinee(), symbols);
        if (path == null) {
            return;
        }
        souther.compiler.coverage.ControlPointId.ArmOccurrence[] arms = plan.armsOf(match);
        for (int i = 0; i < match.cases().size(); i++) {
            Core.Case arm = match.cases().get(i);
            if (NormalReturn.of(arm.body())) {
                continue;
            }
            if (arms == null || i >= arms.length) {
                continue;   // a fork this plan holds no arms for is one nothing can be asked about
            }
            souther.compiler.coverage.ControlPointId.ArmOccurrence where = arms[i];
            List<UnreachableReasons.Said> said = UnreachableReasons.said(arm.body());
            List<String> why = said.stream().map(UnreachableReasons.Said::reason).distinct().toList();
            // Cases written together on one arm are one run of code, and it declares the same thing
            // about every one of them.
            arm.caseTypes().forEach(each -> found.add(new Claim(path, each, why,
                    said.get(0).at(), where)));
        }
    }

    public boolean isEmpty() {
        return claims.isEmpty();
    }

    /** Every claim, in the order the body makes them. */
    public List<Claim> all() {
        return claims;
    }


}
