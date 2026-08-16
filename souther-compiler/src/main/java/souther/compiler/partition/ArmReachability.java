package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.Admits;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The arms of a body that the model's own rules prove nothing reaches.
 *
 * <p>One fact, derived once, read by every measure. What a position is divided into, which lines are
 * owed a row, which arms are owed a row and which cases the signature is owed are four projections of
 * one universe of possible executions, and four derivations of what is possible are four chances to
 * disagree — which is how a report came to drop the class beyond a cap while still asking for the arm
 * behind it.
 *
 * <p>Two rules, and both are the same reading of the input answering a question about a fork.
 *
 * <p>A {@code guard} arm goes when the comparison it turns on cannot come out that way for any value
 * the position admits. A {@code match} arm goes when the case it matches is one the rules refuse at
 * the position matched on — {@code data Active = Flag invariant value /= Off} leaves no {@code Off}
 * to arrive, so the arm written for one is an arm nothing reaches and no row is owed at it. That
 * holds at any depth, and it is the one direction that does: a refusal is unconditional, so it is as
 * true under three enclosing arms as it is at the first fork, while a case the rules <em>admit</em>
 * says nothing about whether the fork it belongs to is reached.
 *
 * <p><b>Only proof excludes.</b> An arm this does not name may still be unreachable — a rule outside
 * what the reading could take in can refuse every value of an overlap — and that direction is the
 * safe one: an arm left in is one the report asks for, and an author reading an obligation they
 * cannot meet has at least been told something true about their model.
 *
 * <p>What a body <em>declares</em> unreachable reaches none of this. An arm answering
 * {@code unreachable} is not an arm at all, which the body says on its own (spec
 * §an-arm-that-answers-nothing-is-not-an-arm); an arm declaring that a case cannot arrive is a claim,
 * held against this same reading somewhere else and never read into it.
 */
public final class ArmReachability {

    /** Nothing proven: every arm is owed whatever it was owed. */
    public static final ArmReachability NONE = new ArmReachability(Set.of());

    private final Set<Integer> unreachable;

    private ArmReachability(Set<Integer> unreachable) {
        this.unreachable = unreachable;
    }

    /**
     * <p>Held by probe number, which is what a branch obligation is counted by: the sites of a module
     * are numbered across all of its bodies, so one number names one arm of one behavior and a caller
     * matching on it cannot reach another behavior's. Which behavior an edge is in is on the edge
     * itself, for a caller that needs to say.
     *
     * @param edges      both arms of every guard whose comparison could be read
     * @param read       what can arrive at each position of the input, which is where both rules get
     *                   their answer — the numbers a comparison is held against and the cases a
     *                   {@code match} arm is written for
     */
    public static ArmReachability of(List<GuardEdge> edges, Core body, CoverageSites.Plan plan,
                                     InputDomain read, Symbols symbols) {
        Set<Integer> out = new LinkedHashSet<>();
        Map<NumericTerm, NumericDomain.Bounds> admissible = numbers(read);
        for (GuardEdge edge : edges) {
            if (edge.provenDisjoint(admissible.get(edge.term()))) {
                out.add(edge.site());
            }
        }
        armsAt(body, plan, InputReads.of(read), symbols, out);
        return out.isEmpty() ? NONE : new ArmReachability(Set.copyOf(out));
    }

    /** What the rules leave each term's values, which is what a comparison is proven against. */
    private static Map<NumericTerm, NumericDomain.Bounds> numbers(InputDomain read) {
        Map<NumericTerm, NumericDomain.Bounds> out = new LinkedHashMap<>();
        for (Position position : read.positions()) {
            if (position.numericDomain() != null && !position.numericDomain().isEmpty()) {
                out.put(position.term(), position.numericDomain());
            }
        }
        return out;
    }

    /**
     * Every {@code match} arm written for a case the rules refuse at the position matched on.
     *
     * <p>The whole body and not its first fork. Which cases a position can hold is a fact about the
     * position, so it is as true of a {@code match} written three arms deep as of the one at the top
     * — what depth costs is the other direction, where being able to arrive at a position says
     * nothing about whether this fork is reached.
     *
     * <p>Cases written together on one arm are one arm, so an arm goes only where every case it
     * names is refused: an arm a row can still take is an arm the rows are owed.
     *
     * <p>Which reads are the input's is asked of their bindings, so a lambda binding a name a
     * parameter already binds is matched on for what it is rather than for what it is spelled.
     */
    private static void armsAt(Core body, CoverageSites.Plan plan, InputReads reads,
                               Symbols symbols, Set<Integer> out) {
        if (body == null) {
            return;
        }
        if (body instanceof Core.Match match) {
            TermPath path = reads.pathOf(match.scrutinee(), symbols);
            Position at = path == null ? null : reads.read().at(path);
            int[] arms = at == null ? null : plan.probesOf(match);
            for (int i = 0; arms != null && i < match.cases().size() && i < arms.length; i++) {
                if (arms[i] != CoverageSites.NO_SITE && refusesEvery(at, match.cases().get(i))) {
                    out.add(arms[i]);
                }
            }
        }
        // Inside what a `let` binds, so that an arm of an expanded helper is read against the
        // position the call handed it.
        InputReads inside = body instanceof Core.LetIn let ? reads.and(let.binder(), let.value())
                : reads;
        Core.forEachChild(body, child -> armsAt(child, plan, inside, symbols, out));
    }

    /** Whether the rules refuse every case this arm is written for. An arm naming none of them —
     *  a binding of the whole value — is not one of these. */
    private static boolean refusesEvery(Position at, Core.Case arm) {
        List<TypeSymbol> named = arm.caseTypes();
        return !named.isEmpty()
                && named.stream().allMatch(each -> at.admissionOf(each) instanceof Admits.Refused);
    }

    /**
     * The same, with these arms no longer proven.
     *
     * <p>What takes a proof away is a row that went through the arm. Nothing about the model is wrong
     * then — the proof is — and a caller reading this afterwards has to be told the same thing every
     * other caller is, or the arm leaves one denominator and stays out of another.
     */
    public ArmReachability without(Set<Integer> sites) {
        if (sites.isEmpty() || unreachable.isEmpty()) {
            return this;
        }
        Set<Integer> left = new LinkedHashSet<>(unreachable);
        left.removeAll(sites);
        return left.isEmpty() ? NONE : new ArmReachability(Set.copyOf(left));
    }

    /** Whether nothing reaches the arm with this probe number. */
    public boolean provenUnreachable(int site) {
        return unreachable.contains(site);
    }

    /** The arms nothing reaches, by probe number. */
    public Set<Integer> unreachableSites() {
        return unreachable;
    }

    public boolean isEmpty() {
        return unreachable.isEmpty();
    }
}
