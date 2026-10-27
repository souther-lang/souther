package souther.compiler.check;

import souther.compiler.values.AdmissibleValues;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * Which readings took each clause into their own semantics.
 *
 * <p>Recorded where each reading runs, and by that reading. A caller working out from a clause's
 * spelling which reading ought to have managed it is guessing at another reader's semantics — which
 * is the defect this exists to stop, one level over from the one it was written for: an ordering
 * bound is unreadable to the reading that turns clauses into sets of values and is read whole by two
 * others, and the shape says nothing about which of them managed it.
 *
 * <p>Per clause, because that is the granularity a question has. Asked per position, one clause's
 * failure is the account of every clause beside it: {@code invariant floor = value >= 1} leaves the
 * reading of values short at a position, and {@code invariant seven = value == 7} written beside it
 * was taken in whole and came back reported as unread.
 *
 * <p>Filed under {@link RuleRef} and not under the clause reference the walk had in hand. Every
 * clause reaching here is an invariant's, so the two would key the same map today — and the value
 * recorded here is carried to a report, where what names a rule is the rule. Weakened on the way
 * out, each reader downstream had to work the identity back out for itself.
 *
 * <p>Success and not attempt. A reading that recognised part of a clause and gave up took nothing
 * in, so nothing here records it — what is written down is the point at which a reading adopted the
 * clause into what it holds.
 *
 * <p>Every part of the clause, and not one of them. A conjunction is one rule the author wrote and
 * is read one conjunct at a time; a clause half of which nothing took in is a clause nothing took
 * in, and answering it on the strength of the half that was read is how {@code value >= 1 &&
 * value * value >= 4} came back with nothing to say while the same two rules written apart were
 * reported. The same reading {@code Predicates.Owed.and} makes of a clause it could not read all
 * of.
 *
 * <p><b>Every reading, and each one asked at its own adoption point.</b> There are more of them than
 * a reader notices: {@code value * 2 >= 4} is beyond the reading of ends and beyond the reading of
 * values, and the reading that builds the numeric constraints takes it in whole. An accounting that
 * consulted two of the three would report that clause exactly the way #842 reports a bound — as a
 * rule this compiler could not read, about a model it had read.
 */
final class ReadingEvidence {

    /** Where each reading took a clause in. */
    private final Map<RuleRef.Invariant, Set<FactSubject>> spokenFor = new LinkedHashMap<>();

    /** Where a part of a clause was taken in by nothing, which no other part makes up for. */
    private final Map<RuleRef.Invariant, Set<FactSubject>> left = new LinkedHashMap<>();

    /**
     * Which statements some reading took in, and at which positions: what the reading of values was
     * stopped by in one of these is no account of the rule ({@link #stoppedBy(RuleRef.Invariant,
     * Collection)}).
     *
     * <p>Statements and not conjuncts. A helper's body joining two rules is one conjunct stating
     * both, and one of them taken in says nothing of the other — recorded under the conjunct, what
     * stopped the reading of values in the one left standing went with the one taken in, and the
     * question stood with nothing to say for it.
     */
    private final Set<StatementAt> statementsTaken = new HashSet<>();

    /**
     * What stopped the reading of values at each position of each rule.
     *
     * <p>Under the rule, which is what makes it an account of a rule rather than of a place. Two
     * clauses reach one position and stop this reading in two ways — a pattern nothing takes apart
     * beside an ordering it has no set for — and a reason filed under the position alone answers
     * for whichever of them a report happens to ask about. The rule that was actually short of it
     * is then named beside a limit that belongs to its neighbour.
     *
     * <p>Empty for a rule this reading took in, and empty as well for one it was short of without
     * recording why. The second is what {@link #stoppedBy} answers for.
     *
     * <p><b>Facts and not a map of positions to reasons.</b> Each of these says the written place
     * the reading decided it at as well as the position and the reason, and a map keyed by position
     * has nowhere to put the third — two choices of one rule each offering an alternative nothing
     * could read leave one position open, and an author has two of them to look at. Held as reasons
     * per position they were one, and which of the two a reader was sent to was whichever the walk
     * met first.
     *
     * <p>A set, because nothing here is in an order anybody may read. Which of two an author wrote
     * first is the source's to say and is asked where a document is written.
     */
    private final Map<RuleRef.Invariant, Map<RuleShortfall, Set<InvariantStatementId>>>
            stopped = new LinkedHashMap<>();

    /**
     * Where the arithmetic stopped on a part of each rule that nothing took in.
     *
     * <p>Beside what stopped the reading of values and not inside it. That reading says what it
     * could not take apart in its own vocabulary, and the arithmetic says where it stopped in the
     * vocabulary a line nobody drew is told in; a part nothing took in was given up on by both, and
     * either is a thing that would have to change.
     */
    private final Map<RuleRef.Invariant, Set<FormShortfall>> formStopped = new LinkedHashMap<>();

    /**
     * Which statements the arithmetic stopped on, at which positions nothing took them in.
     *
     * <p>The statement is what says which comparison it was. One that compares is that comparison
     * and nothing else, and it is the one identity both readings file under — the construct a
     * comparison was written as is no identity for one nobody wrote, which every such comparison
     * shares, and the place it stands in holds as many comparisons as the conjunct states.
     */
    private final Set<StatementAt> formStoppedAt = new HashSet<>();

    /** The places each rule defines a number from and so leaves as free as they were. */
    private final Map<RuleRef.Invariant, Set<FactSubject>> freed = new LinkedHashMap<>();
    /** The rules that say something besides what places are defined as. */
    private final Set<RuleRef.Invariant> statingMore = new HashSet<>();

    /** A reading took {@code rule} in at {@code position}. */
    void record(RuleRef.Invariant rule, FactSubject position) {
        spokenFor.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).add(position);
    }

    /**
     * The places {@code rule} defines a number from, which it leaves as free as they were.
     *
     * <p>Taken in all the same: a rule that restricts none of the positions it names has nothing
     * left standing about them, and what the arithmetic could not say of it is not what stands
     * between the rule and its positions.
     */
    void freedByDefinition(RuleRef.Invariant rule, Collection<FactSubject> positions) {
        freed.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).addAll(positions);
        positions.forEach(position -> record(rule, position));
    }

    /** {@code rule} says something besides the places it defines as numbers. */
    void statesMoreThanDefinitions(RuleRef.Invariant rule) {
        statingMore.add(rule);
    }

    /** Whether {@code rule} says nothing but that places are defined as numbers made of places it
     *  leaves free ({@link #freedByDefinition}). */
    boolean isOnlyDefining(RuleRef rule) {
        return freed.containsKey(rule) && !statingMore.contains(rule);
    }


    /** Whether {@code rule} leaves {@code position} as free as it was, being a place its
     *  definition of another is made of ({@link #freedByDefinition}). */
    boolean isFreedByDefinition(RuleRef.Invariant rule, FactSubject position) {
        Set<FactSubject> here = freed.get(rule);
        return here != null && here.contains(position);
    }

    /**
     * Whether a part of {@code rule} about one of {@code positions} was taken in by nothing.
     *
     * <p>Outranks every other answer about the rule. A clause half of which nothing read is a clause
     * nothing read, however well the other half went — so an end placed by one conjunct does not
     * answer for the conjunct beside it.
     */
    boolean anyLeftStanding(RuleRef.Invariant rule, Collection<FactSubject> positions) {
        Set<FactSubject> standing = left.get(rule);
        return standing != null && positions.stream().anyMatch(standing::contains);
    }

    /** A part of {@code rule} was taken in by nothing, of the positions it named. */
    void leftStanding(RuleRef.Invariant rule, Set<FactSubject> positions) {
        left.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).addAll(positions);
    }

    /** Some reading took {@code statement} in at {@code position}. */
    void tookInStatement(InvariantStatementId statement, FactSubject position) {
        statementsTaken.add(new StatementAt(statement, position));
    }

    /** A statement of a rule, at one position. */
    private record StatementAt(InvariantStatementId statement, FactSubject position) {}

    /**
     * What the reading of values made of {@code rule}, as that reading recorded it.
     *
     * <p>Taken from the reading of this one clause and before it is met with the rest. What is met
     * is a set of values, and the reasons of every clause meet with it — so a caller asking the
     * whole what stopped it at a position is asking about the position and hearing whichever rule
     * reached it.
     *
     * <p><b>What the reading wrote down where it wrote it, and never a position's answer read
     * back.</b> What arrives is a {@link RuleShortfall}, made where the reading still had the
     * written place in hand. {@link AdmissibleValues#standing} answers for the position and is
     * deliberately not the source of this: it holds the reasons of every rule that reached the
     * place and names none of them, so an account built out of it is a list of reasons and no
     * clause. {@link AdmissibleValues#whyUnread} reads that record against the set the alternatives
     * arrived at and answers a third question — whether the set at a position is as narrow as the
     * rules leave it — and parts company with both exactly where a choice covers a position: the
     * set is exact and nothing is answerable for it, and the rule is still one nobody took in.
     *
     * <p><b>And only what a rule is answerable for.</b> Everything filed here is filed under a rule,
     * so a reason about no rule may not arrive: an allowance run down by everything a position
     * admits is a fact about the answer, and the same rules in another order would have been built.
     * Nothing is asked here because nothing of the wrong kind can be made: what arrives is refused
     * where it would be built, which is one fact away from where a caller could have written it.
     *
     * @param in the statement it was decided in, held beside the fact and not in it: one choice a
     *           helper wrote, copied into two conjuncts, is one fact decided in both
     */
    void stoppedBy(RuleRef.Invariant rule, RuleShortfall read, InvariantStatementId in) {
        stopped.computeIfAbsent(rule, _ -> new LinkedHashMap<>())
                .computeIfAbsent(read, _ -> new LinkedHashSet<>()).add(in);
    }

    /**
     * Everything the reading of values was stopped by, of {@code rule} at any of {@code positions},
     * in a conjunct no other reading took in.
     *
     * <p>Every name the position answers to, as {@link #tookIn} asks: a clause reaching it is filed
     * under whichever the reading recognised. Empty where this reading recorded nothing of the
     * rule there, which a caller has to answer for rather than fill in from the position.
     *
     * <p>A statement some other reading took in was given up on by this reading all the same, and
     * that is no account of a question the statement beside it left standing: {@code value >= 0 &&
     * Int.floorMod(value, 1000) == 0} is left standing by the remainder, and the ordering beside it
     * was taken in by the reading of ends. One fact decided in several statements — a choice a
     * helper wrote, copied into each — is kept where any of them was taken in by nothing.
     */
    Set<RuleShortfall> stoppedBy(RuleRef.Invariant rule, Collection<FactSubject> positions) {
        Map<RuleShortfall, Set<InvariantStatementId>> here = stopped.get(rule);
        if (here == null) {
            return Set.of();
        }
        Set<RuleShortfall> out = new LinkedHashSet<>();
        here.forEach((each, in) -> {
            if (positions.contains(each.position()) && in.stream().anyMatch(statement ->
                    !statementsTaken.contains(new StatementAt(statement, each.position())))) {
                out.add(each);
            }
        });
        return out;
    }

    /** The arithmetic stopped on {@code statement} of {@code rule}, which nothing took in. */
    void stoppedOnTheForm(RuleRef.Invariant rule, FormShortfall stoppedOn,
                          InvariantStatementId statement) {
        formStopped.computeIfAbsent(rule, _ -> new LinkedHashSet<>()).add(stoppedOn);
        formStoppedAt.add(new StatementAt(statement, stoppedOn.position()));
    }

    /**
     * Which of {@code these} were decided only in comparisons the arithmetic stopped on, at the
     * position each is about.
     *
     * <p>Every statement a fact was decided in that nothing took in, and not some of them. One fact
     * decided in two — a helper's comparison copied into two conjuncts — is true of both, and the
     * arithmetic stopping on one of them says nothing of the other.
     */
    Set<RuleShortfall> decidedWhereTheArithmeticStopped(RuleRef.Invariant rule,
                                                        Set<RuleShortfall> these) {
        Map<RuleShortfall, Set<InvariantStatementId>> here = stopped.getOrDefault(rule, Map.of());
        Set<RuleShortfall> out = new LinkedHashSet<>();
        for (RuleShortfall each : these) {
            Set<InvariantStatementId> in = here.getOrDefault(each, Set.of());
            boolean any = false;
            boolean all = true;
            for (InvariantStatementId statement : in) {
                StatementAt at = new StatementAt(statement, each.position());
                if (!statementsTaken.contains(at)) {
                    any = true;
                    all &= formStoppedAt.contains(at);
                }
            }
            if (any && all) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * Where the arithmetic stopped on a part of {@code rule} nothing took in, at any of
     * {@code positions} — every name the position answers to, as {@link #stoppedBy} asks.
     */
    Set<FormShortfall> stoppedOnTheForm(RuleRef.Invariant rule,
                                        Collection<FactSubject> positions) {
        Set<FormShortfall> here = formStopped.get(rule);
        if (here == null) {
            return Set.of();
        }
        Set<FormShortfall> out = new LinkedHashSet<>();
        here.forEach(each -> {
            if (positions.contains(each.position())) {
                out.add(each);
            }
        });
        return out;
    }

    /**
     * Whether anything took {@code rule} in, of a position named by any of {@code positions}.
     *
     * <p>Every name the position answers to, since a number is called one thing by the interval
     * algebra and another by everything else, and a clause reaching it is filed under whichever the
     * reading recognised.
     */
    boolean tookIn(RuleRef.Invariant rule, Collection<FactSubject> positions) {
        if (anyLeftStanding(rule, positions)) {
            return false;
        }
        Set<FactSubject> here = spokenFor.get(rule);
        return here != null && positions.stream().anyMatch(here::contains);
    }
}
