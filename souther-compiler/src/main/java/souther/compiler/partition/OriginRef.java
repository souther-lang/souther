package souther.compiler.partition;

import souther.compiler.source.SourceId;

import souther.compiler.check.RuleRef;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;

/**
 * A rule of the model, as a boundary reader met it.
 *
 * <p>{@link RuleRef} and what is true of it here. Which rule it is is the same value however many
 * times the rule is read, and everything beside it on these records is an answer about this reading
 * of it: where the comparison's own value is recorded, which arms witness it, which side of the
 * line the cut value falls on, which declarations took an end in. None of those tell one rule from
 * another, and a question keyed on them is a question the reading raised rather than the model.
 *
 * <p>Three identities and not one, because they are three equivalences. {@link RuleRef} answers
 * whose rule it is; this answers which reading of that rule a boundary was drawn off; and
 * {@link BoundaryLine} answers which of them a partition folds into one line. A guard inside a
 * helper is read once per call: those are several of these, one {@code RuleRef}, and one line.
 *
 * <p>Kept per cut rather than per axis. Several rules can put a cut at the same value — a type's
 * invariant and a {@code guard} that repeats it, or two guards written in different behaviors — and
 * they merge into one partition while staying separate obligations. Reaching the boundary through one
 * guard says nothing about the other.
 */
public sealed interface OriginRef {

    /**
     * A clause of a {@code data}'s invariant, as the clause it is.
     *
     * <p>The clause and not the end it placed. This used to be the declaration together with the
     * word {@code min} or {@code max}, which says what the clause did: two clauses of one
     * declaration bounding a position at one value came out as one origin, and the cut kept one
     * rule where ADR-0090 says it keeps every rule that drew it.
     *
     * @param holdsAtTheValue whether the cut value is one the bound admits, which is the end's own
     *                        inclusivity and is what says whether a row at the cut is the border's
     *                        {@code ON} point or its {@code OFF} point. Carried for the same reason
     *                        a guard's origin carries it: nothing downstream can work it back out.
     *                        A discrete carrier steps a strict bound onto the value it leaves, so
     *                        {@code value > 5} on an {@code Int} arrives as an inclusive 6; a
     *                        continuous one has no step, so {@code value > 5.0m} on a
     *                        {@code Decimal} arrives here as an exclusive 5. Both are built. No
     *                        report shows the second today, because a cut on a continuous carrier
     *                        goes no further than this — which is a fact about how far the
     *                        derivation gets and not one about the end, and reading the end is what
     *                        keeps the two from being confused if it ever does get further
     */
    record InvariantOrigin(RuleRef.Invariant rule, boolean holdsAtTheValue) implements OriginRef {

        public InvariantOrigin {
            if (rule == null) {
                throw new IllegalArgumentException("a bound drawn by no clause");
            }
        }
    }

    /**
     * A comparison written in a behavior's body.
     *
     * <p>The comparison and not what tests it. Meeting this boundary takes more than writing the
     * value — the comparison has to have been evaluated, and a row can hand the behavior the exact
     * threshold and never get there — and where that is recorded is the comparison's own place.
     * Nothing about a fork is here at all. One comparison given a name can be consumed by two forks
     * and by none, so a reading that took anything from a fork would be answering which of them the
     * rule really belongs to — a question with no answer. What a use of the truth proves about the
     * comparison is not modelled, because no measure asks it: a row meets the line by lighting the
     * comparison's own probe.
     *
     * @param rule              which comparison, which is the rule and the whole of it
     * @param read              which reading of that rule this is, and where it was met
     * @param valueBelongsBelow which side of the line the cut value itself is on. It decides which
     *                          neighbour is the other class's edge: {@code <= 3000} leaves 3001 over
     *                          there, {@code < 3000} leaves 2999.
     * @param holdsAtTheValue   whether the comparison is true at the line's own value. Not derivable
     *                          from {@code valueBelongsBelow}: {@code x <= c} and {@code x > c} agree
     *                          about the class the value is in and disagree here
     */
    record ComparisonOrigin(RuleRef.Comparison rule, Read read, boolean valueBelongsBelow,
                            boolean holdsAtTheValue, boolean singles) implements OriginRef {

        public ComparisonOrigin(RuleRef.Comparison rule, Read read, boolean valueBelongsBelow,
                                boolean holdsAtTheValue) {
            this(rule, read, valueBelongsBelow, holdsAtTheValue, false);
        }

        /**
         * Which reading of the comparison this is, and where that reading was.
         *
         * <p>None of it tells one rule from another. A comparison inside a non-recursive helper is
         * read once per call of that helper, so one comparison the author wrote arrives as several
         * of these — each a real occurrence, each measured on its own, and all of them the same
         * rule.
         *
         * <p>No fork. What a row met the line by is getting the comparison to answer, and the
         * comparison is where that is recorded — so the arms of the {@code if} standing round it
         * were a second place the same reading could be taken from, and one that has nothing to say
         * about a comparison written where no fork stands round it.
         *
         * @param comparison which comparison this reads. Required, and this is what meeting the line
         *              is measured against: a row met it by getting the comparison to answer, which
         *              is not what any arm records. A condition stops as soon as it is settled, so
         *              under {@code A && B} the arm where the condition failed holds rows that made
         *              {@code B} false and rows that never reached {@code B}. The comparison and not
         *              the number it is instrumented under — two readers agreeing that they mean one
         *              place should not come down to their having been handed the same int
         * @param written how a reader finds the rule: the construct it stands in and the place it is
         *              written. The comparison's own place and not the fork's — a condition holding
         *              three comparisons is three rules, and a reader sent to the {@code if} is
         *              given one handle for all of them
         */
        public record Read(souther.compiler.coverage.ComparisonOccurrence comparison,
                           souther.compiler.check.RuleCitation.WrittenAt written) {}

    }

    /**
     * A comparison written in a behavior's {@code ensures}.
     *
     * <p>The third rule that draws a line, and neither of the other two. Like an invariant it is met
     * by writing the value: what a clause states is a relation the behavior is held to, so the line
     * is covered by the input the relation changes at and there is no site to look for it at —
     * whether some run of the clause reached that comparison is another question and not the one a
     * boundary measures. Like a guard the line has values on both sides — {@code id.value > 0} under
     * a {@code NotFound} arm says the behavior may not answer that case at or below zero and may
     * above it, so a row is owed either side — which is what tells it from a bound, where nothing
     * outside can be constructed at all.
     *
     * <p>Only a comparison on an input is here. One reading {@code value} is a line on the answer,
     * and a row cannot be written at it: what a row chooses is what the behavior is applied to, not
     * what it answers with. Nothing turns such a comparison away; a term over the answer names no
     * position of the input, so it draws nothing.
     *
     * <p>Both shapes of line wear this. A line at a count of one position and a line between two
     * are drawn by the same rules and are met the same way, so what tells them apart is the target
     * and not the origin — and a reader asking which rule is owed this row does not have to know
     * which shape the line has.
     *
     * @param rule              which clause of which behavior — the rule and the whole of it
     * @param valueBelongsBelow which side of the line the cut value itself is on, which decides
     *                          which neighbour is the other class's edge
     * @param holdsAtTheValue   whether the comparison is true at the line's own value. Not derivable
     *                          from {@code valueBelongsBelow}, and what tells one line of a rule
     *                          from another written at the same value: {@code id.value <= 5} and
     *                          {@code id.value > 5} agree about the class the value is in and are
     *                          two things a row on the line shows apart. On a line between two
     *                          positions it is the whole of what the row shows, since there is no
     *                          class either side to read instead
     * @param singles           whether the comparison singles the value out rather than ordering
     *                          the values either side of it
     */
    record EnsuresOrigin(RuleRef.Ensures rule, boolean valueBelongsBelow,
                         boolean holdsAtTheValue, boolean singles) implements OriginRef {}

    /**
     * A bound one rule put there and another took in.
     *
     * <p>One obligation and not two. The rules do not each want a row: {@code MinuteOfDay}'s maximum
     * is why this position has an upper edge at all, and {@code WorkInterval}'s clause is why that
     * edge is 1439 rather than 1440. Kept as two origins side by side they would be counted as two
     * boundaries at one value, which is the accounting for rules that each drew a line of their own
     * — an invariant and a guard naming the same number — and not for one line two rules settled
     * together.
     *
     * @param bound  the rule that put an edge here
     * @param within the declarations whose own clauses decided where it stopped, and not the value
     *               the position sits in: the same relation can be written on the record, on a
     *               record inside it, or on a name wrapped round either, and only the one that wrote
     *               it has anything to answer for. Several where taking any one of them away leaves
     *               the end where it is, since each is then as much the answer as the others and
     *               choosing would invent the one that is not known
     */
    record NarrowedOrigin(OriginRef bound, List<TypeSymbol> within) implements OriginRef {

        public NarrowedOrigin {
            within = List.copyOf(within);
            if (within.isEmpty()) {
                throw new IllegalArgumentException("a bound narrowed by nothing is not narrowed");
            }
        }
    }

    /**
     * Which rule of the model this is a reading of, through however many narrowings.
     *
     * <p>The same value for every reading of one rule, which is what makes it a key. What a
     * narrowing adds is about the end and not about the rule: {@code MinuteOfDay}'s maximum is the
     * rule whether or not {@code WorkInterval} moved where it lands, so it comes back the same here
     * and is kept beside it by whoever is measuring the line.
     */
    default RuleRef rule() {
        return switch (this) {
            case InvariantOrigin i -> i.rule();
            case ComparisonOrigin g -> g.rule();
            case EnsuresOrigin e -> e.rule();
            case NarrowedOrigin n -> n.bound().rule();
        };
    }

    /**
     * Where this came from, as a report writes it, with the sources under the names {@code names}
     * gives them and the section it is printed under being about {@code sectionSource}.
     *
     * <p>A guard has no name, so what identifies it is where it is written — and that is a place, so
     * it is said the way every other place a report names is said. Its own file where that is not the
     * section's, and the declaration it is written in where this compile has no source for it. Built
     * from the place instead, one compile reported a guard of {@code Int.abs} as {@code guard@7:22}
     * two lines under an arm of that same body saying where it was.
     *
     * <p>Which word the place is written under is the construct the author wrote, taken off the
     * origin the fork carries rather than off the lowered node. Three constructs draw a line this way
     * and one of them is spelled {@code guard}, so a report that called all three that sent two of
     * their readers looking for a form that is not there.
     *
     * <p>A type and an invariant have names, and a name is the same wherever it is read, so they take
     * no resolver and are given one only because this is one question.
     */
    default String describe(SourceNameResolver names, SourceId sectionSource) {
        return switch (this) {
            case InvariantOrigin i -> i.rule().named();
            case EnsuresOrigin e -> e.rule().named();
            // The same word and the same join a question about this rule is written with. A rule
            // and a line it drew are found the same way, and two spellings of one place read as two
            // places.
            case ComparisonOrigin g -> g.read().written().said(names, sectionSource);
            case NarrowedOrigin n -> n.bound().describe(names, sectionSource) + " within "
                    + n.within().stream().map(TypeSymbol::name)
                            .collect(java.util.stream.Collectors.joining(" or "));
        };
    }

    /**
     * The same rule, named without a place.
     *
     * <p>What a diagnostic's own sentence says. A diagnostic is built where no reader is — nothing
     * there knows what to call a source — so a place written into its text would be a line and a
     * column with no file, read against whichever file the report happens to be about. Where the rule
     * is a guard, the place is pointed at instead, by {@link #citation}.
     */
    default String named() {
        return switch (this) {
            case InvariantOrigin i -> i.rule().named();
            case EnsuresOrigin e -> e.rule().named();
            // The construct the source wrote, which the rule cannot say: a comparison is written
            // rather than named, and which fork tests it is a fact about this reading of it. Never
            // rendered to a reader either way — a rule with no name gets a sentence of its own, and
            // the catalog holds those words in every language rather than this building one.
            case ComparisonOrigin _ -> "the " + souther.compiler.check.RuleCitation.WHAT_IT_IS;
            // A narrowing is not part of the rule, so it is said here and not by the rule.
            case NarrowedOrigin n -> n.bound().named() + " within "
                    + n.within().stream().map(TypeSymbol::name)
                            .collect(java.util.stream.Collectors.joining(" or "));
        };
    }

    /**
     * Whether this rule is found by where it is written rather than by what it is called.
     *
     * <p>What every caller wants of it, and what it used to ask instead was which construct of the
     * language drew the line. Three constructs put a line on a condition and one of them is spelled
     * {@code guard}, so a predicate reading as the keyword answered {@code true} about an
     * {@code if} — and a comparison given a name a line above the fork that tests it stands under
     * no fork at all while being the same rule.
     *
     * <p>Asked rather than matched on the text: what a rule is called is a rendering, and two of
     * them read the same word.
     */
    default boolean isWrittenRatherThanNamed() {
        return switch (this) {
            case ComparisonOrigin _ -> true;
            case NarrowedOrigin n -> n.bound().isWrittenRatherThanNamed();
            case InvariantOrigin _, EnsuresOrigin _ -> false;
        };
    }

    /** Where the rule is written, where it is a rule that has a place rather than a name. */
    default java.util.Optional<Citation> citation() {
        return switch (this) {
            case ComparisonOrigin g -> java.util.Optional.of(g.read().written().at());
            case NarrowedOrigin n -> n.bound().citation();
            case InvariantOrigin _, EnsuresOrigin _ -> java.util.Optional.empty();
        };
    }

    /**
     * Which comparison a row has to get an answer out of, for a rule that meeting takes more than
     * writing the value.
     *
     * <p>Asked of the rule rather than matched on which kind it is, because the two are not the same
     * question and reading one for the other is what puts a new rule on whichever arm the code was
     * written next to. A guard's line is about control flow: the comparison is a place in a body, a
     * value can arrive at the behavior's input without arriving there, and a row met the line by
     * getting it to answer — the site is where that is recorded. Every other rule states something
     * about the values themselves. An invariant refuses everything outside its bound, so nothing
     * exists that could have missed it; a clause states a relation, and what covers where the
     * relation changes is the input written at it. For those, writing the value is the whole of what
     * there is to reach and there is no comparison to look at.
     */
    default java.util.Optional<souther.compiler.coverage.ComparisonOccurrence> comparisonAt() {
        return switch (this) {
            case ComparisonOrigin g -> java.util.Optional.of(g.read().comparison());
            case NarrowedOrigin n -> n.bound().comparisonAt();
            case InvariantOrigin _, EnsuresOrigin _ -> java.util.Optional.empty();
        };
    }

}
