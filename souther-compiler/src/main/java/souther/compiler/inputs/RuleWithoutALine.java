package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;
import souther.compiler.check.RuleReportAnchor;
import souther.compiler.types.ModelOccurrences;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * One rule of the model, at one position it is about, that this did not turn into a line.
 *
 * <p>Asked of the rule, and it names one. One position carries more than one statement, and a line
 * read at it says nothing about the rest — a threshold on {@code x} does not answer for the bound
 * beside it that nothing could read. Carrying only the position, the sentence written from this
 * told an author that a rule about {@code r.cost} went unread and left them to find which rule; and
 * two rules with no line at one position came out as one line, which is what a finding asked of the
 * rule may not do.
 *
 * <p><b>Whichever rule drew it.</b> A {@code guard}'s comparison, a newtype's invariant and a
 * clause of an {@code ensures} are three producers of one kind of evidence (spec
 * §example-partition), so a reader of this list is told the same thing about any of them and does
 * not have to know which wrote it. Named after the guard while only guards produced one, an
 * invariant nothing could read had nowhere to be said and was dropped in silence — the position
 * then came back as one the model divides no way, which is the opposite of what the declaration
 * says.
 *
 * <p>The rule once, and the questions that place it beside it. What a reader groups by is the rule
 * ({@link Fact}); what an author acts on is a handle, which is that rule together with one of those
 * questions, and {@link #cited} makes them rather than keeping them. Kept, a handle would be a
 * second answer to which rule this is about, free to be of another one.
 *
 * <p><b>Named for what is true of everything in it.</b> Two opposite things bring a rule here — one
 * this compiler got partway through, and one it read from end to end that draws no line — and what
 * they have in common is the whole of what this says: at this position, this rule is no line. Which
 * of the two it was is {@code why}, and it is asked of the type rather than read back out of a
 * word.
 *
 * <p><b>And neither of them is what holds a measure of coverage open.</b> That is a question about
 * a rule, which the reading that classifies the rule raises; this is what a report says about what
 * became of a rule here. Counted as the first, a rule this compiler read completely is one nobody
 * could read.
 *
 * @param fact      which rule, at which position, and why there is no line — the whole of what makes
 *                  two of these one finding ({@link Fact})
 * @param reachedBy every question a reader was offered for the rule, because a rule found by two
 *                  readers is one finding and each of them says how to reach it; which of them a
 *                  document writes is that document's to decide. Empty exactly where the author
 *                  named the rule, which is found by that name from anywhere
 * @param readAt    every copy of the model's code the rule was read at here, for the reason
 *                  {@code reachedBy} is every handle: a rule written in a helper is read once per
 *                  call of it and found alike at each, and the calls are what tell those readings
 *                  apart for a reader. No part of the fact, which is one however many calls found it
 */
public record RuleWithoutALine(Fact fact, Set<RuleReportAnchor> reachedBy,
                               ModelOccurrences readAt) {

    public RuleWithoutALine {
        if (fact == null || readAt == null) {
            throw new IllegalArgumentException("a rule is without a line somewhere, and for a"
                    + " reason");
        }
        reachedBy = reachedBy == null ? Set.of() : Set.copyOf(reachedBy);
        RuleCitation.requireReached(fact.rule(), reachedBy);
    }

    /** One reader's finding about the whole of a rule, as that reader produced it. */
    public static RuleWithoutALine of(RuleCitation cited, FilingCoordinate at,
                                      BlockReason.RuleWithoutLineReason why) {
        return of(cited, ModelOccurrences.NONE, at, RuleSite.theRuleItself(), why);
    }

    /** The same, of a reading made at {@code readAt}, which says which copies of the model's code
     *  it was read at. */
    public static RuleWithoutALine of(RuleCitation cited, ModelOccurrences readAt,
                                      FilingCoordinate at,
                                      BlockReason.RuleWithoutLineReason why) {
        return of(cited, readAt, at, RuleSite.theRuleItself(), why);
    }

    /** The same, for a reader with a place inside the rule to send anybody to. */
    public static RuleWithoutALine of(RuleCitation cited, FilingCoordinate at,
                                      RuleSite sentTo,
                                      BlockReason.RuleWithoutLineReason why) {
        return of(cited, ModelOccurrences.NONE, at, sentTo, why);
    }

    /** The same, read at {@code readAt}. */
    public static RuleWithoutALine of(RuleCitation cited, ModelOccurrences readAt,
                                      FilingCoordinate at, RuleSite sentTo,
                                      BlockReason.RuleWithoutLineReason why) {
        return new RuleWithoutALine(new Fact(cited.rule(), at, sentTo, why),
                RuleCitation.anchorOf(cited), readAt);
    }

    /**
     * A rule with no line here, with the handle for it left out, which is the whole of what makes
     * two of them one.
     *
     * <p>The citation is no part of it. A rule and the handle for it are two questions, and a key
     * holding the handle files one rule under several wherever the two come apart — which they do
     * wherever a rule has no name of its own.
     *
     * <p><b>{@link RuleSite} is part of it, and is not that.</b> Where inside the rule a reader
     * goes is what tells two findings about one clause apart when everything else about them
     * agrees: a clause two parts of which choices left open is two things to lift, and both are
     * the same rule, at the same position, for the same reason. Left out, the second of them was
     * merged into the first and the entry named neither part.
     */
    public record Fact(RuleRef rule, FilingCoordinate at, RuleSite sentTo,
                       BlockReason.RuleWithoutLineReason why) {

        public Fact {
            if (rule == null || at == null || sentTo == null || why == null) {
                throw new IllegalArgumentException("a rule is without a line somewhere, and for a"
                        + " reason");
            }
        }

        /**
         * What tells two findings apart: all of this, with the figures its reason was met at left
         * out. One rule refused at one limit by one reading and at another by the next is one
         * finding, met at both ({@link BlockReason#factOf}).
         */
        public Object key() {
            return List.of(rule, at, sentTo, BlockReason.factOf(why));
        }
    }

    /** Which rule of the model this is about. */
    public RuleRef rule() {
        return fact.rule();
    }

    /** The position it is about, spelled the way a report names it. */
    public FilingCoordinate at() {
        return fact.at();
    }

    /** Why there is no line here, in this compiler's own terms. */
    public BlockReason.RuleWithoutLineReason why() {
        return fact.why();
    }

    /** Where inside the rule a reader goes about it. */
    public RuleSite sentTo() {
        return fact.sentTo();
    }

    /**
     * How a reader finds it — a name where the author gave one, a place where they did not.
     *
     * <p>Made from the rule and the places rather than kept beside them. A handle is the rule
     * together with where it was reached, so made here it is of this finding's rule and can be of no
     * other ({@link RuleCitation}).
     */
    public Set<RuleCitation> cited() {
        return RuleCitation.handlesFor(fact.rule(), reachedBy);
    }

    /**
     * Both readers' findings, as one: the rule, with every place either of them reached it at and
     * every figure either met its reason at.
     *
     * <p>Of one rule, and it says so rather than taking the caller's word. Two that are not one
     * fact would come out as one of them reached where the other was.
     */
    public RuleWithoutALine mergedWith(RuleWithoutALine other) {
        if (!fact.key().equals(other.fact.key())) {
            throw new IllegalArgumentException("two findings put together are one rule with no"
                    + " line: " + fact + " and " + other.fact);
        }
        Set<RuleReportAnchor> both = new HashSet<>(reachedBy);
        both.addAll(other.reachedBy);
        return new RuleWithoutALine(new Fact(fact.rule(), fact.at(), fact.sentTo(),
                BlockReason.together(fact.why(), other.fact.why())), both,
                readAt.and(other.readAt));
    }

}
