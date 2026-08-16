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
 * <p><b>Every claim the body makes about a position of its input, and what reaching it takes.</b>
 * A {@code match} on an input position, wherever it is written, has an arm per case, and an arm
 * that answers nothing is that case being declared not to arrive. What is read off each is the same;
 * what differs is what stands above it, and that is carried rather than decided
 * ({@link Claim.Standing}) — the fork the body reaches first is reached whenever the behavior is
 * applied, and one inside another arm is reached under a condition nothing here reads.
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
    public static UnreachableClaims of(Core body, InputDomain read, Symbols symbols) {
        if (body == null) {
            return NONE;
        }
        List<Claim> found = new ArrayList<>();
        // The fork this body reaches first, and the whole body walked once. Named by identity
        // rather than by where it sits in a shape, because what makes it the first is the order
        // things run in.
        Core first = firstFork(body);
        claimedUnder(body, InputReads.of(read), symbols,
                first instanceof Core.Match match ? match : null, found);
        return found.isEmpty() ? NONE : new UnreachableClaims(found);
    }

    /**
     * The fork evaluation reaches first however the body goes, or null where it reaches none.
     *
     * <p>An order and not a shape. What a {@code let} binds runs before the body it binds it for,
     * so a {@code match} written as a binding's value is the first thing this body does — read as a
     * shape, the walk stepped over it to the end of the spine and called a later fork the first
     * one, which let a claim at the fork every caller reaches escape being refused.
     *
     * <p>A fork's own arms are not entered. What runs before a fork is its scrutinee or its
     * condition, and what runs after is whichever arm was taken, which is the thing being decided.
     */
    private static Core firstFork(Core e) {
        if (e == null) {
            return null;
        }
        if (e instanceof Core.Match match) {
            Core inScrutinee = firstFork(match.scrutinee());
            return inScrutinee != null ? inScrutinee : match;
        }
        if (e instanceof Core.If iff) {
            Core inCondition = firstFork(iff.cond());
            return inCondition != null ? inCondition : iff;
        }
        if (e instanceof Core.IfConstructed ic) {
            Core inConstruction = firstIn(Evaluated.inOrder(ic.construct()));
            return inConstruction != null ? inConstruction : ic;
        }
        return firstIn(Evaluated.inOrder(e));
    }

    private static Core firstIn(List<Core> evaluated) {
        for (Core each : evaluated) {
            Core found = firstFork(each);
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /**
     * Every claim under {@code e}, each standing behind whatever arm it is written in.
     *
     * <p>One walk over the body. Which fork is the one nothing stands above is settled before it
     * starts and asked by identity here, because that is a fact about where the fork sits and not
     * about what it looks like.
     */
    private static void claimedUnder(Core e, InputReads reads, Symbols symbols, Core.Match first,
                                     List<Claim> found) {
        if (e == null) {
            return;
        }
        InputReads inside = e instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        if (e instanceof Core.Match match) {
            claimedIn(match, inside, symbols,
                    match == first ? new Claim.Standing.Reached()
                            : new Claim.Standing.Conditional(),
                    found);
        }
        Core.forEachChild(e, child -> claimedUnder(child, inside, symbols, first, found));
    }

    /**
     * What one {@code match} declares, and the scrutinee it declares it about.
     *
     * <p>Says nothing where the scrutinee names no position of this input: there is nothing to
     * claim about, and what is under its arms is walked by the caller either way.
     */
    private static void claimedIn(Core.Match match, InputReads reads, Symbols symbols,
                                  Claim.Standing standing, List<Claim> found) {
        TermPath path = reads.pathOf(match.scrutinee(), symbols);
        if (path == null) {
            return;
        }
        for (Core.Case arm : match.cases()) {
            if (NormalReturn.of(arm.body())) {
                continue;
            }
            List<UnreachableReasons.Said> said = UnreachableReasons.said(arm.body());
            List<String> why = said.stream().map(UnreachableReasons.Said::reason).distinct().toList();
            // Cases written together on one arm are one run of code, and it declares the same thing
            // about every one of them.
            arm.caseTypes().forEach(each -> found.add(new Claim(path, each, why,
                    said.get(0).at(), standing)));
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
