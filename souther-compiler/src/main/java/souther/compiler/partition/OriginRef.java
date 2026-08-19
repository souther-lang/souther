package souther.compiler.partition;

import souther.compiler.source.SourceId;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Optional;

/**
 * Where a partition or a boundary came from.
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
     */
    record InvariantOrigin(souther.compiler.check.Clause.Ref rule) implements OriginRef {

        public InvariantOrigin {
            if (rule == null) {
                throw new IllegalArgumentException("a bound drawn by no clause");
            }
        }
    }

    /**
     * A comparison in a behavior's body, and the {@code if} it is the condition of.
     *
     * <p>The guard is kept, not just the position, because meeting this boundary takes more than
     * writing the value: the comparison has to have been evaluated. A row can hand the behavior the
     * exact threshold and never reach the guard that cares about it.
     *
     * @param guard             which {@code if} — by the arms it owns, which is what says which
     *                          class of the partition a row landed in
     * @param site              where the comparison's own value is recorded. Required, and this is
     *                          what meeting the line is measured against: a row met it by getting the
     *                          comparison to answer, which is not what any arm records. A condition
     *                          stops as soon as it is settled, so under {@code A && B} the arm where
     *                          the condition failed holds rows that made {@code B} false and rows
     *                          that never reached {@code B}
     * @param valueBelongsBelow which side of the line the cut value itself is on. It decides which
     *                          neighbour is the other class's edge: {@code <= 3000} leaves 3001 over
     *                          there, {@code < 3000} leaves 2999.
     * @param witness           which arms of the {@code if} a row reaching this comparison can land
     *                          in. Not what says the comparison ran — {@code site} is — but what says
     *                          which arm's edge is this comparison's to draw, which is a question
     *                          about the classes either side of the line
     * @param holdsAtTheValue   whether the comparison is true at the line's own value. Not derivable
     *                          from {@code valueBelongsBelow}: {@code x <= c} and {@code x > c} agree
     *                          about the class the value is in and disagree here
     */
    record GuardOrigin(souther.compiler.coverage.CoverageSites.GuardRef guard, int site,
                       souther.compiler.coverage.CoverageSites.Obligation comparison,
                       Citation at, boolean valueBelongsBelow,
                       Witness witness,
                       boolean holdsAtTheValue, boolean singles) implements OriginRef {

        public GuardOrigin(souther.compiler.coverage.CoverageSites.GuardRef guard, int site,
                           souther.compiler.coverage.CoverageSites.Obligation comparison,
                           Citation at, boolean valueBelongsBelow,
                           Witness witness,
                           boolean holdsAtTheValue) {
            this(guard, site, comparison, at, valueBelongsBelow, witness, holdsAtTheValue, false);
        }

        /** Which arms a row that reached this comparison can be in. */
        public enum Witness {
            /** Either: the comparison is on the leftmost spine, so it runs whatever the condition
             * comes to. */
            BOTH,
            /** Only the arm the whole condition is true on, which is a conjunction. */
            THEN,
            /** Only the arm it is false on, which is a disjunction. */
            ELSE,
            /** Neither on its own, which a condition mixing {@code &&} and {@code ||} leaves: a row
             * that reached the comparison can be in either arm, so neither arm's edge is this
             * comparison's alone. */
            NEITHER
        }
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
     * @param rule              which rule of which clause, which is what tells one line from
     *                          another. Two arms of one clause may name the same case, so the
     *                          author's words for it are not enough
     * @param clause            what a report calls it: the name the author gave the clause, or the
     *                          case the arm names where they gave none, or empty where the clause
     *                          states one rule over every answer
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
    record EnsuresOrigin(souther.compiler.check.BehaviorContract.RuleId rule, String clause,
                         boolean valueBelongsBelow, boolean holdsAtTheValue,
                         boolean singles) implements OriginRef {}

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
     * What tells one line from another, with nothing in it that says which copy of a body the line
     * was read off.
     *
     * <p>A guard inside a non-recursive helper is read once per call of that helper, so one line the
     * author drew arrives here as several. They carry different arms and a different comparison site
     * — each is a real occurrence and each is measured on its own — and they are one line to write a
     * row at. This is what says which of them are the same one.
     *
     * <p>A rule that is not a guard is its own line: nothing about an invariant or a type is read off
     * a body, so there is nothing here that expansion could have duplicated.
     *
     * @param rule            the origin itself, for the rules that are their own line
     * @param comparison      which comparison of which fork, for a guard's line
     * @param narrowedWithin  the declarations a bound was taken in by, kept so that a narrowed line
     *                        stays apart from the bare one it narrows
     */
    record Line(OriginRef rule, souther.compiler.coverage.CoverageSites.Obligation comparison,
                boolean valueBelongsBelow, GuardOrigin.Witness witness, boolean holdsAtTheValue,
                boolean singles, List<TypeSymbol> narrowedWithin) {}

    /** The line this origin drew, said the way {@link Line} says it. */
    default Line line() {
        return switch (this) {
            case GuardOrigin g -> new Line(null, g.comparison(), g.valueBelongsBelow(), g.witness(),
                    g.holdsAtTheValue(), g.singles(), List.of());
            case NarrowedOrigin n -> {
                Line inner = n.bound().line();
                yield new Line(inner.rule(), inner.comparison(), inner.valueBelongsBelow(),
                        inner.witness(), inner.holdsAtTheValue(), inner.singles(), n.within());
            }
            default -> new Line(this, null, false, null, false, false, List.of());
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
            case InvariantOrigin i -> nameOf(i);
            case EnsuresOrigin e -> nameOf(e);
            case GuardOrigin g -> switch (g.at()) {
                case Citation.Written _, Citation.Unplaced _ ->
                        wordFor(g) + "@" + g.at().said(names, sectionSource);
                case Citation.Elsewhere _ -> wordFor(g) + " in " + g.at().said(names, sectionSource);
            };
            case NarrowedOrigin n -> n.bound().describe(names, sectionSource) + " within "
                    + n.within().stream().map(TypeSymbol::name)
                            .collect(java.util.stream.Collectors.joining(" or "));
        };
    }

    /**
     * What a report calls the construct a line was drawn in.
     *
     * <p>English, like every other word this method writes. What a diagnostic says instead is chosen
     * in the reader's language, from the same construct.
     */
    private static String wordFor(GuardOrigin g) {
        return switch (g.constructThatDrewIt()) {
            case IF -> "if";
            case GUARD -> "guard";
            case COMPREHENSION -> "comprehension";
            // A line is read off a fork's condition, and these are not forks. Reaching one is this
            // reader and the walk that numbered the fork disagreeing about what drew the line.
            case MATCH, BINARY, NOT_WRITTEN -> throw new IllegalStateException(
                    "a line was drawn in something that is not a fork: "
                            + g.guard().origin().kind());
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
            case InvariantOrigin i -> nameOf(i);
            case EnsuresOrigin e -> nameOf(e);
            // Never rendered to a reader: a rule with no name gets a sentence of its own, so the
            // catalog holds those words in every language rather than this building them in one.
            // What reaches this is a caller that wanted something to call the rule anyway, and what
            // it gets is the construct the source wrote rather than one of the three standing for
            // all of them.
            case GuardOrigin g -> "the " + wordFor(g);
            case NarrowedOrigin n -> n.bound().named() + " within "
                    + n.within().stream().map(TypeSymbol::name)
                            .collect(java.util.stream.Collectors.joining(" or "));
        };
    }

    /**
     * What a report calls a clause: the behavior, and the words that tell one of its rules from
     * another.
     *
     * <p>A name and not a place, which is what puts it beside an invariant rather than beside a
     * guard. A clause belongs to a behavior, so there is always something to call it — where the
     * author named the clause it is that name, and where they did not it is the case the arm is
     * about. Only a clause stating one rule over every answer has neither, and the behavior's own
     * name is then the whole of it.
     */
    private static String nameOf(InvariantOrigin i) {
        // What the author called it, and where they called it nothing, which of the declaration's
        // clauses it is — counted from one, as somebody reading the declaration counts them. Two
        // unnamed clauses of one declaration are two rules, and rendered by the declaration alone
        // they are one word twice, which is the thing this origin was changed to stop.
        return "invariant " + i.rule().id().declaredOn().name()
                + i.rule().name().map(n -> " (" + n + ")")
                        .orElse(" #" + (i.rule().id().ordinal() + 1));
    }

    private static String nameOf(EnsuresOrigin e) {
        return "ensures " + e.rule().behavior().name()
                + (e.clause().isEmpty() ? "" : " (" + e.clause() + ")");
    }

    /**
     * Whether a fork of a body drew this line, through however many narrowings.
     *
     * <p>Not whether the author wrote {@code guard}. Three constructs put a line on a condition and
     * one of them is spelled that way, so a predicate reading as the keyword would be answered
     * {@code true} about an {@code if} — and the next reader to notice the mismatch would repair the
     * name into a test of the construct and break the other two. What this separates is a rule with a
     * place from a rule with a name, which is what every caller wants of it.
     *
     * <p>Asked rather than matched on the text: what a rule is called is a rendering, and two of them
     * read the same word.
     */
    default boolean wasDrawnInABodyFork() {
        return switch (this) {
            case GuardOrigin _ -> true;
            case NarrowedOrigin n -> n.bound().wasDrawnInABodyFork();
            case InvariantOrigin _, EnsuresOrigin _ -> false;
        };
    }

    /**
     * Which construct of the language drew this line, through however many narrowings.
     *
     * <p>Asked of the rule rather than worked out from the shape the fork was lowered to. Three
     * constructs draw a line off a condition and one of them is spelled {@code guard}; the tree that
     * runs holds one node for all three, and the answer travels with the fork's origin from where the
     * source was read.
     *
     * @throws IllegalStateException where no fork drew the line. An invariant and a clause have
     *                               names rather than places, and {@link #wasDrawnInABodyFork} is
     *                               what tells them apart from this
     */
    default souther.compiler.types.CoverageConstruct constructThatDrewIt() {
        return switch (this) {
            case GuardOrigin g -> g.guard().origin().kind();
            case NarrowedOrigin n -> n.bound().constructThatDrewIt();
            case InvariantOrigin _, EnsuresOrigin _ -> throw new IllegalStateException(
                    "no fork of a body drew this line: " + named());
        };
    }

    /** Where the rule is written, where it is a rule that has a place rather than a name. */
    default java.util.Optional<Citation> citation() {
        return switch (this) {
            case GuardOrigin g -> java.util.Optional.of(g.at());
            case NarrowedOrigin n -> n.bound().citation();
            case InvariantOrigin _, EnsuresOrigin _ -> java.util.Optional.empty();
        };
    }

    /**
     * Where the comparison's own value is recorded, for a rule that meeting takes more than writing
     * the value.
     *
     * <p>Asked of the rule rather than matched on which kind it is, because the two are not the same
     * question and reading one for the other is what puts a new rule on whichever arm the code was
     * written next to. A guard's line is about control flow: the comparison is a place in a body, a
     * value can arrive at the behavior's input without arriving there, and a row met the line by
     * getting it to answer — the site is where that is recorded. Every other rule states something
     * about the values themselves. An invariant refuses everything outside its bound, so nothing
     * exists that could have missed it; a clause states a relation, and what covers where the
     * relation changes is the input written at it. For those, writing the value is the whole of what
     * there is to reach and there is no site to look at.
     */
    default java.util.OptionalInt comparisonSite() {
        return switch (this) {
            case GuardOrigin g -> java.util.OptionalInt.of(g.site());
            case NarrowedOrigin n -> n.bound().comparisonSite();
            case InvariantOrigin _, EnsuresOrigin _ -> java.util.OptionalInt.empty();
        };
    }

    /**
     * The value beside the cut a row is owed as well, or nothing where the line has no other side.
     *
     * <p>The second of the two questions, and independent of the first. What decides it is whether
     * the values either side of the line are both writable: a guard and a clause leave a range on
     * each side, and a bound leaves nothing outside itself, so an invariant's edge is the only row
     * there is to write. A value a rule singles out has no neighbour either — the values either side
     * of it are one class, so a row over there is a row that class already has.
     *
     * <p>Which neighbour it is comes from where the cut value itself falls: {@code <= 3000} leaves
     * 3001 over the line and {@code < 3000} leaves 2999.
     */
    default java.util.Optional<BoundaryObligation.BoundarySide> besideTheCut() {
        return switch (this) {
            case GuardOrigin g -> g.singles() ? java.util.Optional.empty()
                    : java.util.Optional.of(g.valueBelongsBelow()
                            ? BoundaryObligation.BoundarySide.ABOVE
                            : BoundaryObligation.BoundarySide.BELOW);
            case EnsuresOrigin e -> e.singles() ? java.util.Optional.empty()
                    : java.util.Optional.of(e.valueBelongsBelow()
                            ? BoundaryObligation.BoundarySide.ABOVE
                            : BoundaryObligation.BoundarySide.BELOW);
            case NarrowedOrigin n -> n.bound().besideTheCut();
            case InvariantOrigin _ -> java.util.Optional.empty();
        };
    }
}
