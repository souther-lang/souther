package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * What the parts of a rule left a question standing on.
 *
 * <p><b>And no order.</b> Reasons stand in the order their author wrote the things they are about,
 * and saying which that is needs the source: what is here is which construct each of them is about
 * ({@link RuleSite}), counted over what the author wrote and holding no place at all. A carrier
 * that claimed an order would be claiming one over numbers nobody wrote — the ordinals a construct
 * is identified by are a function of the owner's syntax and are deliberately not the order it is
 * written in ({@code SourceConstructOrigin}) — so the claim is made where the places are, which is
 * the one boundary that has them ({@code AdequacyReport}).
 *
 * <p>It used to be made here, out of the positions each reason stood on. That is what put a place
 * inside every answer a reading published, and what made an edit moving a declaration an edit that
 * changed what the model says.
 *
 * <p>Held in a steady order all the same, and that order is asserted of nothing: it is what keeps
 * one compiler over one source publishing one document. Held in the order a walk met them, the same
 * compiler over the same source would publish two, and which one an author saw would be the run
 * they happened to make.
 *
 * <p>So what is held is {@link Said} and not a word. Two reasons alike about two things inside one
 * rule are two things to lift, and a list of words says they are one.
 *
 * @param said each reason, what it is about, and where inside the rule it sends a reader
 */
public record RuleReasons(List<Said> said) {

    public RuleReasons {
        said = List.copyOf(said);
    }

    /**
     * The same, as the words alone, each once.
     *
     * <p>For a reader asking what a question stands on rather than where to go about it — whether a
     * wider run gets past it, which is a question about the kinds of thing and not about their
     * places. A caller counting these is counting kinds: two choices of one clause leave one word
     * here and two entries in {@link #said()}.
     */
    public List<BlockReason.RuleReadingStopped> reasons() {
        Map<Object, BlockReason.RuleReadingStopped> out = new LinkedHashMap<>();
        for (Said each : said) {
            out.merge(BlockReason.factOf(each.reason()), each.reason(), BlockReason::together);
        }
        return List.copyOf(out.values());
    }

    /**
     * Whether these and {@code other} say one thing: the same reasons about the same things, with
     * the figures each was met at left out ({@link BlockReason#factOf}).
     */
    public boolean sameFactAs(RuleReasons other) {
        return facts().equals(other.facts());
    }

    /**
     * Both, as one, where they say one thing: every figure either met each reason at.
     *
     * <p>Refused where they say different things, which {@link #sameFactAs} asks.
     */
    public RuleReasons together(RuleReasons other) {
        if (!sameFactAs(other)) {
            throw new IllegalArgumentException(
                    "two accounts put together say one thing: " + this + " and " + other);
        }
        List<Said> both = new ArrayList<>(said);
        both.addAll(other.said);
        return from(both);
    }

    /** As a set: the order these are held in is steady and asserted of nothing. */
    private Set<Object> facts() {
        return said.stream().map(Said::fact).collect(Collectors.toSet());
    }

    /** Whether the question stands on nothing its rule left. */
    public boolean isEmpty() {
        return said.isEmpty();
    }

    /**
     * One reason, what it is about, and where inside the rule a reader is sent about it.
     *
     * <p>What tells two of these apart, and all three are needed for it. Two parts of one clause
     * stopped by one limit are one thing to lift and one of these; one clause whose ends two
     * choices left open is two, and nothing in the word says so.
     *
     * <p>{@code about} and {@code sentTo} are two answers and not one. What a reading decided about
     * is the construct its author wrote, which is what puts two of these in the order they were
     * written; where a reader goes about it is the whole rule for most of what this compiler is
     * short of, and a part of one for the rest. Held as one, a reason about a form nothing reads
     * would either send a reader inside a rule they have to rewrite whole, or lose the only thing
     * that says which form it was.
     *
     * @param about  what the reading decided it about, as its author wrote it
     * @param sentTo where inside the rule the reader goes — the rule itself for a reason about the
     *               whole of it, and something in it for one about a part
     * @param reason what the reading was short of, in this compiler's own terms
     */
    public record Said(RuleSite about, RuleSite sentTo, BlockReason.RuleReadingStopped reason) {

        /** The reason, what it is about and where it sends a reader, each by the whole of it. */
        static final Comparator<Said> IN_A_STEADY_ORDER =
                Comparator.comparing(Said::reason, BlockReason.RuleReadingStopped.IN_A_STEADY_ORDER)
                        .thenComparing(Said::about, RuleSite.IN_A_STEADY_ORDER)
                        .thenComparing(Said::sentTo, RuleSite.IN_A_STEADY_ORDER);

        public Said {
            if (about == null || sentTo == null || reason == null) {
                throw new IllegalArgumentException(
                        "a reason is about something, and says where a reader goes about it");
            }
        }

        /** What tells this from another, with the figures its reason was met at left out. */
        Object fact() {
            return List.of(about, sentTo, BlockReason.factOf(reason));
        }

        private Said together(Said other) {
            return new Said(about, sentTo, BlockReason.together(reason, other.reason));
        }
    }

    /**
     * These, each once, in a steady order that is nobody's.
     *
     * <p>Told apart by the reason, by what it is about and by where it sends a reader, which is
     * what makes two choices of one clause two entries. Kept by the word alone — which is what this
     * did while a word was the whole of what travelled — the second of them was dropped as a repeat
     * of the first.
     *
     * <p><b>Steady, and that is all it is.</b> Nothing here says which of two reasons an author
     * wrote first; what settles that is where they wrote them, and that is asked where the places
     * are. What the order must not be is the one a walk happened to meet them in: a projection out
     * of this reaches a document, so a sequence left to the walk would have one compiler over one
     * source publish two.
     *
     * <p>So each of them is compared by the whole of what it is — the word, what it is about, and
     * where it sends a reader — and each of those by the whole of what <em>it</em> is
     * ({@link BlockReason.RuleReadingStopped#IN_A_STEADY_ORDER}, {@link RuleSite#IN_A_STEADY_ORDER}).
     * Two of these are left in the order they arrived in only where they are one value, and a set
     * holds one of those.
     *
     * <p>Two that say one thing but for the figures their reason was met at are one entry, met at
     * every one of those figures: a rule refused at one limit by one reading and at another by the
     * next is one thing for a reader to lift.
     */
    public static RuleReasons from(List<Said> these) {
        Map<Object, Said> once = new LinkedHashMap<>();
        these.forEach(each -> once.merge(each.fact(), each, Said::together));
        List<Said> sorted = new ArrayList<>(once.values());
        sorted.sort(Said.IN_A_STEADY_ORDER);
        return new RuleReasons(List.copyOf(sorted));
    }

    /** One reason about the whole of its rule, which is most of what this compiler is short of. */
    public static RuleReasons one(BlockReason.RuleReadingStopped reason) {
        return one(RuleSite.theRuleItself(), reason);
    }

    /** The same, for a reader that has something inside the rule to send anybody to. */
    public static RuleReasons one(RuleSite sentTo, BlockReason.RuleReadingStopped reason) {
        return new RuleReasons(List.of(new Said(sentTo, sentTo, reason)));
    }
}
