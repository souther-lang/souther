package souther.compiler.check;

import souther.compiler.inputs.BlockReason;

import java.util.List;
import java.util.SequencedMap;
import java.util.Set;

/**
 * What one clause of an invariant states, as the reading that ran over it found it.
 *
 * <p>The input the obligations a clause raises are a function of, and package-private so that they
 * stay one: a value of this comes from a reader that looked at the clause, and outside this package
 * there is no way to make one. Which is what keeps {@link Required.Irrelevant} from being a sentence
 * anybody can write — saying that a rule raises no question at all is a conclusion about the model,
 * and the only thing entitled to draw it is a reading of the rule.
 *
 * <p>Three answers and not a tally of what a reader could do with the clause. Each says what the
 * clause is about; none of them says whether this compiler managed anything with it, which is the
 * other question and is {@link InvariantBound.Read}'s. The two used to be one: {@code AnEnd} was
 * built where {@code InvariantBound.at} came back with an end, so a bound this could not fold — the
 * {@code 20} in {@code value <= 10 * 2} — arrived here as a clause that states no bound at all.
 * {@code NoValueAtAll} was the same mixing from the other side, reached only by folding the bound
 * and comparing it against the carrier's order.
 *
 * <p>Each carries what it is about, taken from the same reading. Worked out again where the
 * questions are raised, the subject a question is filed under and the subject the reading found
 * would be two answers about one clause.
 *
 * <p><b>What a clause is about, and not the questions it raises.</b> A place it names is a
 * {@link RuleKey} and a line it draws is a {@link NumberAt}, which are what a reading
 * of a clause has; which coverage question each of them becomes is {@link Required#ofInvariant}'s
 * and is decided there. Written in the vocabulary of the questions instead, the names were a set of
 * subjects every member of which was the same arm with the same flag — a set of names wearing the
 * type of a set of subjects, so that a lookup by name read as a comparison of subjects.
 */
sealed interface ClauseStates {

    /**
     * The clause states where the values stop on one or more of the numbers it writes about.
     *
     * <p>What states it is not said here. A coordinate compared for order against an expression
     * naming no coordinate of this value does; so does a rule admitting a run of the strings at a
     * position, which is no comparison and has no sides. What is common is what the clause says —
     * that the values stop somewhere on a number it names — and this is that and nothing about the
     * shape it was written in.
     *
     * <p>Whether an end came of it is not asked here, and neither is whether the order has a value
     * at the end. A rule states where the values stop by stating it; what this compiler made of the
     * number on the other side is what answers the question, not what raises it.
     *
     * <p><b>The lines are a set, and a clause can state one on a number while leaving another
     * undecided.</b> One clause is read a branch at a time and the branches are joined, so what it
     * comes to is an answer per number — held as a single line, a clause bounding two of them had
     * to be refused or picked between, and one bounding one number while nothing settled the next
     * lost the second question entirely.
     *
     * @param lines the numbers the clause stops the values on. Each is the value at a name or a
     *              number an operation answers of it — the operation itself, since two operations
     *              over one name are two lines and a flag saying one was taken cannot tell them
     *              apart
     * @param named the ones the clause is about, which is what a rule can cost. Never empty: a
     *              clause bounding a coordinate writes the name it sits at
     * @param unread the names whose line nothing worked out, and what stopped it. A clause can
     *              state a line on one number and leave whether it states one on another standing,
     *              and the second is a question with no answer rather than one nobody asked
     */
    record ABound(Set<NumberAt<RuleKey>> lines, Set<RuleKey> named,
                  SequencedMap<RuleKey, List<BlockReason.RuleReadingStopped>> unread)
            implements ClauseStates {

        public ABound {
            if (lines.isEmpty()) {
                throw new IllegalArgumentException("a bound is a line on some number");
            }
            if (named.isEmpty()) {
                throw new IllegalArgumentException("a bound is written about a name of the value");
            }
            lines = java.util.Collections.unmodifiableSet(
                    new java.util.LinkedHashSet<>(lines));
            named = java.util.Collections.unmodifiableSet(
                    new java.util.LinkedHashSet<>(named));
            unread = java.util.Collections.unmodifiableSequencedMap(
                    new java.util.LinkedHashMap<>(unread));
            for (NumberAt<RuleKey> each : lines) {
                if (!named.contains(each.position())) {
                    throw new IllegalArgumentException("`" + each + "` is a line on a name this"
                            + " clause does not write: " + named);
                }
            }
        }

        /** One line on one number, which is what a comparison states. */
        ABound(NumberAt<RuleKey> line, Set<RuleKey> named) {
            this(Set.of(line), named, new java.util.LinkedHashMap<>());
        }

        /** The line this clause stops the values on at {@code name}, or null where it states
         *  none there. */
        NumberAt<RuleKey> lineAt(RuleKey name) {
            for (NumberAt<RuleKey> each : lines) {
                if (each.position().equals(name)) {
                    return each;
                }
            }
            return null;
        }
    }

    /**
     * How what stands at one name compares with another.
     *
     * <p>{@code startsAt < endsAt}, {@code a /= b}. Nothing about it was beyond the reading — both
     * sides were recognised — and a set of one name's values is not what it says, so it raises
     * no question about one. What it settles is settled beside the partition rather than in
     * it (ADR-0090).
     */
    record ARelation() implements ClauseStates {}

    /**
     * The clause restricts no value of anything.
     *
     * <p>{@code lo - lo >= 0} holds of every row there is. The quantity it cuts is empty — the
     * number cancels against itself — so there is no value anywhere it admits or refuses,
     * and nothing a measure of coverage could go and check.
     *
     * <p><b>Read off what the rule cuts and not off what the spelling names.</b> The name is
     * written twice in that clause, so counted off the sides it is a rule about that name and
     * raises the questions such a rule raises: which values may stand there, and where
     * they stop. Nothing can answer either, because the rule states neither — so a clause this
     * compiler read from end to end and understood completely came out as a question nobody had
     * answered, and took the measurement to partial with it.
     *
     * <p>Its own state and not {@link SomethingElse} with an empty set of names. That one is a
     * clause about a name written in a shape this classification does not take further, and it
     * carries the names so that whatever reads the clause can be asked about them. This is a
     * conclusion about the clause: it was read, and there is nothing in it to ask anybody about.
     */
    record NoRestriction() implements ClauseStates {}

    /**
     * Something else: the values a rule names, a call, a pattern, an expression the terms do not
     * name.
     *
     * <p>One arm for all of them, because what a clause raises does not turn on which of them it is.
     * A rule about the values at a name is a rule about them whether this compiler can read it
     * or not, and reading the arm as "this compiler failed" is the confusion the whole type exists
     * to stop: the question is raised by the model, and whether anything answered it is asked
     * afterwards.
     *
     * @param named the ones the clause states something about, which may be none. A rule cannot
     *              cost a name it does not write, so these and not every name of the value — and a
     *              clause writing none of them raises no question about one, which is what
     *              {@link Required#ofInvariant} makes of an empty set. Filed at the value instead,
     *              {@code invariant t = 1 >= 0} was a rule nothing had accounted for
     * @param unread the names whose line the reading of the form did not settle, each with what
     *              stopped it, and empty where it ran to the end. A name a clause states an order
     *              about, in a form nothing took apart, may have a line and may not, and which of
     *              those is what reading further would answer; one read to the end that draws no
     *              line draws none, and that is the model.
     *
     *              <p>Per name, because what a rule raises is asked per name. One comparison has
     *              one arithmetic and so answers alike at every name it writes; a clause is as many
     *              comparisons as the author conjoined, and each is read on its own and met here as
     *              its own state. Held as one answer for the clause, a name whose line was settled
     *              would lose it to a name beside it that was not
     */
    record SomethingElse(Set<RuleKey> named,
                         SequencedMap<RuleKey, List<BlockReason.RuleReadingStopped>> unread)
            implements ClauseStates {

        public SomethingElse {
            // Insertion order: `Set.of` and `Set.copyOf` iterate in an order salted once per JVM
            // run, and what is built from these reaches a checked-in document.
            named = java.util.Collections.unmodifiableSet(
                    new java.util.LinkedHashSet<>(named));
            unread = java.util.Collections.unmodifiableSequencedMap(
                    new java.util.LinkedHashMap<>(unread));
        }

        static SomethingElse naming(List<RuleKey> found) {
            return new SomethingElse(new java.util.LinkedHashSet<>(found),
                    new java.util.LinkedHashMap<>());
        }

        /** The same, told which names the reading of the form left a line undecided at, and what
         *  stopped it at each — every reason, since one clause read a branch at a time can be
         *  stopped by one thing in one branch and another in the next. */
        SomethingElse unread(SequencedMap<RuleKey, List<BlockReason.RuleReadingStopped>> why) {
            return why.isEmpty() ? this : new SomethingElse(named, why);
        }
    }

    /** The names this clause states something about, by which a rule can cost one. */
    default Set<RuleKey> about() {
        return switch (this) {
            case ABound bound -> bound.named();
            case SomethingElse other -> other.named();
            // A rule about a pair costs neither of them: what it says is not a set of the values at
            // one name, so there is nothing about one for anything to have read.
            case ARelation _ -> Set.of();
            // And a rule that restricts nothing costs nothing anywhere. Not the same as writing no
            // name — this one writes one and says nothing about it.
            case NoRestriction _ -> Set.of();
        };
    }
}
