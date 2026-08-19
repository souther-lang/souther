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

    private final OriginRef origin;
    private final Required required;
    private final Map<Owed, Outcome> answers;

    private RuleAccounting(OriginRef origin, Required required, Map<Owed, Outcome> answers) {
        this.origin = origin;
        this.required = required;
        this.answers = Collections.unmodifiableMap(answers);
    }

    /**
     * The accounting of {@code origin}, with {@code answered} asked once for each question it
     * raises.
     *
     * <p>The only way to one of these, and not one anything outside this package can take. What is
     * closed here is which questions there are — {@code answered} is asked for them and never
     * handed the map — and closing that while leaving the answers to whoever asked would let a
     * caller hold a genuine {@link Required} beside answers it wrote itself. A reader outside wants
     * a finished accounting, never a way to make one.
     */
    static RuleAccounting of(OriginRef origin, Required required,
                             Function<Owed, Outcome> answered) {
        Map<Owed, Outcome> answers = new LinkedHashMap<>();
        for (Owed each : required.obligations()) {
            Outcome outcome = answered.apply(each);
            if (outcome == null) {
                throw new IllegalStateException(
                        "no reading answered for " + each + " of " + origin);
            }
            answers.put(each, outcome);
        }
        return new RuleAccounting(origin, required, answers);
    }

    /** Which rule of the model, as everything that names a rule names it. */
    public OriginRef origin() {
        return origin;
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
                .map(e -> new Unanswered(origin, e.getKey()))
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
     * <p>The rule as {@link OriginRef}, all the way to the report that names it. Carried as the
     * clause reference the reading had in hand, the one reader of these built an
     * {@code InvariantOrigin} at the last moment — right while only invariants raise a question,
     * and a decision about what a rule is taken by whoever consumed one (issue #852).
     */
    public record Unanswered(OriginRef origin, Owed owed) {}

    @Override
    public String toString() {
        return origin + " " + answers;
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
        record Unaccounted(UnreadReason why) implements Outcome {}
    }

    /** Which reading answered a question. */
    public enum Reader {

        /** The reading that turns a clause into an end a line can be drawn at. */
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
