package souther.compiler.partition;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.SourceRef;
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

    /** The cases of a sum, or the two values of a {@code Bool}: the type itself says the partition. */
    record TypeOrigin(TypeSymbol type) implements OriginRef {}

    /**
     * A clause of a {@code data}'s invariant.
     *
     * @param at empty for a type that arrived from a module compiled elsewhere, whose clause has no
     *           position in this compilation
     */
    record InvariantOrigin(Optional<SourceRef> at, TypeSymbol type, String clause)
            implements OriginRef {

        public InvariantOrigin {
            at = at == null ? Optional.empty() : at;
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
     * <p>A type and an invariant have names, and a name is the same wherever it is read, so they take
     * no resolver and are given one only because this is one question.
     */
    default String describe(SourceNameResolver names, String sectionSource) {
        return switch (this) {
            case TypeOrigin t -> "type " + t.type().name();
            case InvariantOrigin i -> "invariant " + i.type().name() + " (" + i.clause() + ")";
            case GuardOrigin g -> switch (g.at()) {
                case Citation.Written _ -> "guard@" + g.at().said(names, sectionSource);
                case Citation.OutOfSight _ -> "guard in " + g.at().said(names, sectionSource);
            };
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
            case TypeOrigin t -> "type " + t.type().name();
            case InvariantOrigin i -> "invariant " + i.type().name() + " (" + i.clause() + ")";
            // Never rendered to a reader: a rule with no name gets a sentence of its own, so the
            // catalog holds those words in every language rather than this building them in one.
            // What reaches this is a caller that wanted something to call the rule anyway.
            case GuardOrigin _ -> "a guard";
            case NarrowedOrigin n -> n.bound().named() + " within "
                    + n.within().stream().map(TypeSymbol::name)
                            .collect(java.util.stream.Collectors.joining(" or "));
        };
    }

    /** Whether a guard drew this line, through however many narrowings. Asked rather than matched
     *  on the text: what a rule is called is a rendering, and two of them read the same word. */
    default boolean isAGuard() {
        return switch (this) {
            case GuardOrigin _ -> true;
            case NarrowedOrigin n -> n.bound().isAGuard();
            case TypeOrigin _, InvariantOrigin _ -> false;
        };
    }

    /** Where the rule is written, where it is a rule that has a place rather than a name. */
    default java.util.Optional<Citation> citation() {
        return switch (this) {
            case GuardOrigin g -> java.util.Optional.of(g.at());
            case NarrowedOrigin n -> n.bound().citation();
            case TypeOrigin _, InvariantOrigin _ -> java.util.Optional.empty();
        };
    }
}
