package souther.compiler.check;

import souther.compiler.values.UnreadReason;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * One rule of the model, every question it raises, and what answered each.
 *
 * <p>Closed over the questions rather than a list of answers somebody assembled. What can go wrong
 * with a list is that a question is missing from it, and a completeness read off a list with a
 * question missing says the model was accounted for because nobody asked. So the questions come
 * from {@link Required} and the answers are obtained for exactly those, one apiece: a question
 * without an answer, an answer without a question, and two answers to one question are all
 * unreachable rather than checked for.
 *
 * <p>No verdict about the rule. Whether the rule is settled follows from its answers and from the
 * answers to whatever its questions rest on, and that is a derivation over the whole accounting
 * rather than a field here — written as a field, a question blocked by another would have to be
 * marked blocked by whoever noticed, which is a third state anybody can write.
 */
public final class RuleAccounting {

    private final RuleRef rule;
    private final RuleCitation cited;
    private final Required required;
    private final Map<Owed, Outcome> answers;

    private RuleAccounting(RuleRef rule, RuleCitation cited, Required required,
                           Map<Owed, Outcome> answers) {
        this.rule = rule;
        this.cited = cited;
        this.required = required;
        this.answers = Collections.unmodifiableMap(answers);
    }

    /**
     * The accounting of {@code rule}, with {@code answered} asked once for each question it
     * raises.
     *
     * <p>The only way to one of these, and not one anything outside this package can take. What is
     * closed here is which questions there are — {@code answered} is asked for them and never
     * handed the map — and closing that while leaving the answers to whoever asked would let a
     * caller hold a genuine {@link Required} beside answers it wrote itself. A reader outside wants
     * a finished accounting, never a way to make one.
     */
    static RuleAccounting of(RuleRef rule, Required required,
                             Function<Owed, Outcome> answered) {
        return new RuleAccounting(rule, citedAsAClause(rule), required,
                answers(rule, required, answered));
    }

    /** {@code answered} asked once for each question the rule raises, and nothing else. Apart from
     *  the citation, which the two ways in do not find the same way. */
    private static Map<Owed, Outcome> answers(RuleRef rule, Required required,
                                              Function<Owed, Outcome> answered) {
        Map<Owed, Outcome> answers = new LinkedHashMap<>();
        for (Owed each : required.obligations()) {
            Outcome outcome = answered.apply(each);
            if (outcome == null) {
                throw new IllegalStateException(
                        "no reading answered for " + each + " of " + rule);
            }
            answers.put(each, outcome);
        }
        return answers;
    }

    /**
     * How a reader finds a rule this way in can be about.
     *
     * <p>A clause, either kind, and never a comparison. What comes this way is a rule an author
     * wrote a name beside, and a comparison raises nothing this is made of.
     */
    private static RuleCitation citedAsAClause(RuleRef rule) {
        return switch (rule) {
            case RuleRef.Invariant it -> RuleCitation.named(it);
            case RuleRef.Ensures it -> RuleCitation.named(it);
            // A comparison is written rather than named, and it does not come this way at all: what
            // it raises is answered by the reading that raised it, so there is no accounting of one
            // for anybody to build. What such a rule leaves is a finding about the position.
            case RuleRef.Comparison _ -> throw new IllegalArgumentException(
                    "a comparison raises nothing an accounting is made of: " + rule);
        };
    }

    /** Which rule of the model, as everything that names a rule names it. */
    public RuleRef rule() {
        return rule;
    }

    /** How a reader finds it, which is not what tells it from another rule. */
    public RuleCitation cited() {
        return cited;
    }

    /** What it raises. */
    public Required required() {
        return required;
    }

    /** What answered each question, keyed by the question. */
    public Map<Owed, Outcome> answers() {
        return answers;
    }

    /** The questions nothing answered, which is what a report is about. */
    public Set<Owed> unaccounted() {
        return answers.entrySet().stream()
                .filter(e -> e.getValue() instanceof Outcome.Unaccounted)
                .map(Map.Entry::getKey)
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
    }

    /**
     * The same, each carrying the rule that raised it and what stopped the reading.
     *
     * <p>What a reader downstream is owed. A question with no rule beside it can be reported at a
     * position and never named, which is the sentence #842 is about: an author was told that a rule
     * about the position went unread, with nothing saying which rule.
     */
    public List<Unanswered> unansweredQuestions() {
        return answers.entrySet().stream()
                .filter(e -> e.getValue() instanceof Outcome.Unaccounted)
                .map(e -> new Unanswered(rule, cited, e.getKey()))
                .toList();
    }

    /**
     * One question of one rule that nothing answered.
     *
     * <p>No reason beside it. What a reading records about why it stopped is about a position and
     * this is about a rule at a subject, and putting the first here would be a fact at one
     * granularity wearing another's name — which is the shape this whole accounting was written
     * against. A reason belongs here once the readings say why per part of a clause, and until then
     * an absent one is the honest answer.
     *
     * <p>The rule as {@link RuleRef}, all the way to the report that names it. Carried as the
     * clause reference the reading had in hand, the one reader of these built the identity at the
     * last moment — right while only invariants raise a question, and a decision about what a rule
     * is taken by whoever consumed one.
     */
    public record Unanswered(RuleRef rule, RuleCitation cited, Owed owed) {}

    @Override
    public String toString() {
        return rule + " " + answers;
    }

    /** What became of one question. */
    public sealed interface Outcome {

        /**
         * A reading took the rule in and answered this.
         *
         * <p>{@code by} is provenance and nothing else. Which reading answered is worth having for
         * a diagnostic and for anyone working out why an answer is what it is; nothing about
         * whether the model is covered may be read off it, because that is what tying a completeness
         * to the readers there happen to be amounts to.
         */
        record Accounted(Reader by) implements Outcome {}

        /**
         * Nothing took the rule in, so the question stands.
         *
         * <p>{@code why} is this compiler's own account of what stopped it, in the vocabulary of the
         * reading that would have answered. What a document writes for it is a projection made
         * elsewhere: a published word reaching back into what a reading is allowed to record is the
         * coupling this whole arrangement is written against.
         */
        record Unaccounted(Why why) implements Outcome {}
    }

    /**
     * What stopped the reading that would have answered, in that reading's own words.
     *
     * <p>One arm per reading, because they do not share a vocabulary and neither is the other's. The
     * reading that turns clauses into sets of values says which form it could not take apart; the
     * reading that turns a clause into an end says what would have to change before the rule could
     * be a line. Held as one word, a line about an end was written in the words of a set of values —
     * which is the sentence #842 is about, one level down.
     */
    public sealed interface Why {

        /**
         * The reading that turns a clause into a set of values.
         *
         * <p>Everything it was stopped by, in the order the parts of the clause were met. One
         * position is named by as many parts as the author wrote about it, and two of them stop
         * this reading in two ways that are lifted by different work — so a single reason here is a
         * choice among an author's rules, made where the only thing to choose by is which part came
         * first.
         */
        record TheValueReadingSays(List<UnreadReason> why) implements Why {

            public TheValueReadingSays {
                if (why == null || why.isEmpty()) {
                    throw new IllegalArgumentException("a reading that stopped says why");
                }
                why = List.copyOf(why);
            }
        }

        /**
         * The reading that turns a clause into an end a line can be drawn at.
         *
         * <p>Only reasons that say that reading stopped. A rule it took in from end to end answered
         * the question by being read — where it places no line, there is no line to be owed, and
         * where it restricts no value there is nothing to be admitted. Held as either half, a rule
         * this compiler understood completely was one nobody had accounted for, and the measurement
         * went to partial on the strength of it.
         *
         * <p>Everything it was stopped by, in the order the parts of the clause were met. One
         * question about one line is asked by every conjunct that draws it, and it is answered when
         * every one of them has been read — so a part still standing behind another is a second
         * thing to lift and not a repeat of the first.
         */
        record TheEndReadingSays(
                List<souther.compiler.inputs.BlockReason.RuleReadingStopped> why)
                implements Why {

            public TheEndReadingSays {
                if (why == null || why.isEmpty()) {
                    throw new IllegalArgumentException("a reading that stopped says why");
                }
                why = List.copyOf(why);
            }
        }
    }

    /** Which reading answered a question. */
    public enum Reader {

        /**
         * The reading that turns a rule into a line.
         *
         * <p>One word for it wherever the rule is written. A {@code guard}'s comparison and a
         * newtype's bound are two producers of one kind of evidence (spec §example-partition), and
         * a reader told which of them answered would be holding a fact about this compiler's
         * arrangement of readers rather than about the model.
         */
        THE_END_READING,

        /**
         * A reading that holds what a clause says about the values themselves — which values may
         * stand, what range they run over, what the numbers satisfy.
         *
         * <p>One word for however many of them there are. Which reading answered is provenance;
         * telling them apart here would make the set of readings this compiler happens to have into
         * something a reader downstream can act on, and a reading gained or lost would move what a
         * report says about a model nobody edited.
         */
        THE_VALUE_READING
    }
}
