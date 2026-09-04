package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.UnreadReason;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which branches of a choice anybody can be in is the whole declaration's answer, and what a rule
 * left unread is that rule's own.
 *
 * <p>The two pull the reading in different directions and both hold at once. A branch live on its
 * own clause can be impossible under a clause written later, so the decision waits for every clause
 * — and a branch nobody anywhere can be in takes its unread rules with it, since there is no branch
 * for an author to look at. But a clause a neighbour wrote does not read this rule's alternatives
 * for it: whether an alternative of this rule went unread is answered over this rule's clauses
 * alone, or the gap is hidden by a constraint that happens to stand beside it
 * ({@code EveryPartAReadingStoppedOnSaysWhyTest} holds that end).
 *
 * <p>And a branch's fate is aggregated over every place distribution put it. The same written
 * choice stands inside each branch of every choice met with it, live in one place and dead in
 * another — dead is only dead everywhere, and the aggregate cannot depend on the order the clauses
 * were written in.
 */
class AChoiceIsDecidedByEveryClauseAndAnsweredByItsOwnTest {

    private static final String UNREAD_TAG = souther.compiler.ARuleNoReadingTakesIn.about("tag");
    private static final String UNREAD_S = souther.compiler.ARuleNoReadingTakesIn.about("s");

    /**
     * A branch live on its own clause and impossible under the next one.
     *
     * <p>Reading {@code one} alone, both alternatives admit something, and the rule this reading
     * has no word for stands only in the left one. {@code two} then leaves nobody able to be in
     * that branch.
     */
    private static final String A_LATER_CLAUSE_KILLS_A_BRANCH = """
            module demo

            data Pair = { code: String, tag: String }
                invariant one =
                    (code == "a" && UNREAD_TAG)
                    || code == "c"
                invariant two = code == "c"
            """.replace("UNREAD_TAG", UNREAD_TAG);

    /**
     * One written choice standing in both branches of another, live in one and dead in the other.
     *
     * <p>Distribution puts each alternative of {@code b} beside each alternative of {@code a}:
     * {@code x == 0} is impossible beside {@code x == 1} and possible beside {@code x == 0}. Both
     * of {@code b}'s branches are live somewhere, so neither is dead.
     */
    private static final String LIVE_SOMEWHERE_IS_LIVE = """
            module demo

            data N = { x: Int, s: String }
                invariant a = x == 0 || x == 1
                invariant b =
                    (x == 0 && UNREAD_S)
                    || x == 1
            """.replace("UNREAD_S", UNREAD_S);

    /**
     * A branch dead in every place it stands.
     *
     * <p>{@code x == 2} is impossible beside {@code x == 0} and beside {@code x == 1}, so the
     * branch carrying the rule nothing reads is dead everywhere — and only then do its unread
     * rules go with it.
     */
    private static final String DEAD_EVERYWHERE_IS_DEAD = """
            module demo

            data M = { x: Int, s: String }
                invariant a = x == 0 || x == 1
                invariant b =
                    (x == 2 && UNREAD_S)
                    || x == 0 || x == 1
            """.replace("UNREAD_S", UNREAD_S);

    /** The same two rules with the clauses the other way round. */
    private static final String THE_OTHER_CLAUSE_ORDER = """
            module demo

            data M = { x: Int, s: String }
                invariant b =
                    (x == 2 && UNREAD_S)
                    || x == 0 || x == 1
                invariant a = x == 0 || x == 1
            """.replace("UNREAD_S", UNREAD_S);

    /**
     * A question a rule of a dead branch raised is settled, not left standing.
     *
     * <p>The branch is live on its own clause — this is what waiting for every clause buys. Left
     * standing, an author is sent to a rule of a branch their own next clause already forbids.
     */
    @Test
    void aBranchALaterClauseForbidsTakesItsUnreadRulesWithIt() {
        Map<String, List<UnreadReason>> standing =
                byQuestion(read(A_LATER_CLAUSE_KILLS_A_BRANCH, "Pair"));
        assertFalse(standing.containsKey("invariant Pair (one) at tag"),
                "nothing satisfies the branch the pattern is in, so there is no branch to look at");
    }

    /**
     * A branch live beside one alternative of a neighbour is live, however dead it is beside
     * another.
     *
     * <p>Live, so the rule this reading has no word for inside it is still a rule somebody wrote
     * about a branch somebody can be in — the question at {@code s} stands. What would fail here is
     * a fate recorded per place rather than aggregated: whichever copy was settled last would win,
     * the branch would be reported dead, and the question would be settled with it.
     */
    @Test
    void aBranchLiveAnywhereIsLive() {
        Map<String, List<UnreadReason>> standing =
                byQuestion(read(LIVE_SOMEWHERE_IS_LIVE, "N"));
        assertTrue(standing.containsKey("invariant N (b) at s"),
                "somebody can be in the branch, so its unread rule is theirs to look at: "
                        + standing);
    }

    /** Dead is only dead everywhere — and then the unread rule goes with the branch. */
    @Test
    void aBranchDeadEverywhereIsDead() {
        Map<String, List<UnreadReason>> standing =
                byQuestion(read(DEAD_EVERYWHERE_IS_DEAD, "M"));
        assertFalse(standing.containsKey("invariant M (b) at s"),
                "no alternative of `a` admits the branch, so there is no branch to look at");
    }

    /**
     * The aggregate reads the same whichever clause is written first.
     *
     * <p>Written the other way round, the same written choice is distributed into different
     * places in a different order. A fate that depended on either would answer the same model two
     * ways.
     */
    @Test
    void aFateDoesNotTurnOnTheOrderTheClausesWereWritten() {
        assertEquals(byQuestion(read(DEAD_EVERYWHERE_IS_DEAD, "M")),
                byQuestion(read(THE_OTHER_CLAUSE_ORDER, "M")));
    }

    private static final Term.Interner NAMES = new Term.Interner();
    private static final FactSubject CONSTRAINED = FactSubject.of(NAMES.written("constrained"));
    private static final FactSubject SETTLED = FactSubject.of(NAMES.written("settled"));
    private static final FactSubject UNREAD = FactSubject.of(NAMES.written("unread"));

    /**
     * An unread alternative widens what a branch constrained, and not what a dead branch inside it
     * settled.
     *
     * <p>The account's copy of the rule the values join by: a position a dead branch settled holds
     * an answer — the choice imposes nothing there — and a further alternative, read or not,
     * imposes nothing extra either ({@code Adoption.either} draws the same line). Written over the
     * copy's mentions instead, the account held a reason at a settled position that no output
     * happens to show today, which is a lie waiting for its first reader.
     */
    @Test
    void anUnreadAlternativeWidensAConstraintAndNotAnAnswer() {
        StatedByClauses.Part read = new StatedByClauses.Part(
                new Adoption<>(java.util.Set.of(CONSTRAINED), java.util.Set.of(SETTLED),
                        java.util.Set.of(), false),
                Adoption.nothing(), Map.of(), Map.of(), java.util.Set.of());
        StatedByClauses.Part unread = new StatedByClauses.Part(
                new Adoption<>(java.util.Set.of(), java.util.Set.of(), java.util.Set.of(UNREAD),
                        true),
                Adoption.nothing(), Map.of(UNREAD, List.of(UnreadReason.FORM_NOT_READ)), Map.of(),
                java.util.Set.of());

        assertEquals(Map.of(UNREAD, List.of(UnreadReason.FORM_NOT_READ),
                        CONSTRAINED, List.of(UnreadReason.ALTERNATIVE_NOT_READ)),
                read.either(unread).standing(),
                "the constraint is left open and the answer stands");
    }

    /**
     * A fate aggregates the same whichever occurrence comes first — the reasons included.
     *
     * <p>{@code Emptiness.joined} alone being commutative is not enough: the reasons probing two
     * occurrences left behind travel with the fate, and two occurrences of one branch can be
     * stopped by two limits. Kept in the order the occurrences were met, the same model written
     * with its clauses the other way round would say the same reasons in a different order — a
     * neighbouring clause's order, which is no order of this rule's.
     */
    @Test
    void aFateAggregatesTheSameWhicheverOccurrenceComesFirst() {
        // One of each half, because the two are aggregated as two. What a pattern asked for and was
        // refused says which pattern; what the answer was short of says the place and no more.
        Settlement.Sided one = new Settlement.Sided(
                souther.compiler.values.Emptiness.UNDECIDED, Map.of(),
                List.of(new souther.compiler.values.Unbuilt.RuleShortfall<>(UNREAD,
                        souther.compiler.values.AuthoredOccurrence.another(),
                        UnreadReason.PATTERN_TOO_COSTLY)),
                java.util.Set.of());
        Settlement.Sided other = new Settlement.Sided(
                souther.compiler.values.Emptiness.UNDECIDED,
                Map.of(UNREAD, List.of(UnreadReason.EXACT_VALUES_TOO_COSTLY)), List.of(),
                java.util.Set.of());

        assertEquals(one.alsoSeen(other), other.alsoSeen(one),
                "one branch, one aggregate, whichever copy was settled first");
    }

    /** Every question of every rule that nothing answered, and what stopped this reading of it. */
    private static Map<String, List<UnreadReason>> byQuestion(FieldDomains read) {
        Map<String, List<UnreadReason>> out = new LinkedHashMap<>();
        read.accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (outcome instanceof RuleAccounting.Outcome.Unaccounted unaccounted
                            && unaccounted.why()
                                    instanceof RuleAccounting.Why.TheValueReadingSays says) {
                        out.put(((RuleCitation.Named) accounting.cited()).name() + " at " + owed,
                                says.why());
                    }
                }));
        return out;
    }

    private static FieldDomains read(String source, String name) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule at = TypeSymbols.declared(new TypeKey(symbols.module(), name));
        return FieldDomains.of(at,
                RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
