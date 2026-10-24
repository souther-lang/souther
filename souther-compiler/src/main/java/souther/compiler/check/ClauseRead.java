package souther.compiler.check;

import java.util.Objects;

/**
 * A place a clause reads in the value it is written about, and what it reads there.
 *
 * <p>A place and not a field. A rule of an envelope over {@code pending.low} and
 * {@code pending.high} reads two places under {@code pending} and not {@code pending.boss}; said as
 * the field {@code pending}, it would read all three. A newtype's own {@code value} is the value
 * itself ({@link RuleKey#THE_VALUE}), so a rule of a newtype wrapping a record over
 * {@code value.low} reads {@code low} as a rule of the record would.
 *
 * <p>Where the clause reads a chain of fields down from the value, the place is the end of the
 * chain. Where it reads a value some other way — handed whole to an operation, named in a
 * construction — the place is that value whole, and everything under it is read.
 *
 * @param at   where it reads, as the rules of the value call a place in it
 * @param kind what it reads there
 * @param run  for {@link Kind#EACH_ELEMENTS_RUN}, what it reads of an element, as the rules of the
 *             element call a place in it; the element itself for every other kind
 */
public record ClauseRead(RuleKey at, Kind kind, RuleKey run) {

    public ClauseRead {
        Objects.requireNonNull(at, "a clause reads somewhere");
        Objects.requireNonNull(kind, "a clause reads something of where it reads");
        Objects.requireNonNull(run, "a clause reads a place of an element, or the element");
        if (kind != Kind.EACH_ELEMENTS_RUN && !run.isTheValueItself()) {
            throw new IllegalArgumentException("only a read of elements goes down a run: " + kind);
        }
    }

    /** What a clause reads of a place. */
    public enum Kind {

        /** What stands there, and so everything under it. */
        ITS_VALUES,

        /**
         * How many a list, a set or a map there holds, and nothing of which values its elements
         * take: the place is only what a count is taken of ({@code TakenAs.HowManyItHolds}). A
         * string's length is not one of these — which strings there are of a length is which
         * strings there are.
         */
        HOW_MANY_IT_HOLDS,

        /**
         * The fields of each element of the list, set or map there that a run names, and nothing
         * else of the element: what a call saying no two elements share them reads
         * ({@code ElementsApart}).
         */
        EACH_ELEMENTS_RUN,

        /**
         * The member of the map, set or list there that a lookup names, and no other member: what
         * a lookup or a membership test reads ({@code Map.get}, {@code Map.containsKey},
         * {@code Set.contains}, {@code List.contains}). What it looks for is read as any other
         * value the clause reads is; the other members are not read. Of whether the clause wants
         * that member there or wants it missing, or does not turn on it at all, this says
         * nothing.
         */
        A_LOOKED_UP_MEMBER,

        /**
         * The same read, of a lookup the clause cannot be true without: it is false wherever the
         * container holds no member the lookup names. A container the clause holds to such
         * members and to nothing else of it is one any further member can be added to.
         */
        A_MEMBER_THE_CLAUSE_NEEDS
    }
}
