package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;

import java.util.Objects;
import java.util.Optional;

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
 * @param run  for {@link Kind#EACH_ELEMENTS_RUN} and {@link Kind#ELEMENTS_THE_CLAUSE_NEEDS_APART},
 *             what it reads of an element, as the rules of the element call a place in it; the
 *             element itself for every other kind
 * @param member for {@link Kind#A_MEMBER_THE_CLAUSE_NEEDS}, the member it needs where what the
 *             lookup looks for is a place of the value; empty where it is anything else, and for
 *             every other kind
 */
public record ClauseRead(RuleKey at, Kind kind, RuleKey run, Optional<Member> member) {

    public ClauseRead {
        Objects.requireNonNull(at, "a clause reads somewhere");
        Objects.requireNonNull(kind, "a clause reads something of where it reads");
        Objects.requireNonNull(run, "a clause reads a place of an element, or the element");
        Objects.requireNonNull(member, "a member a clause needs, or none");
        if (kind != Kind.EACH_ELEMENTS_RUN && kind != Kind.ELEMENTS_THE_CLAUSE_NEEDS_APART
                && !run.isTheValueItself()) {
            throw new IllegalArgumentException("only a read of elements goes down a run: " + kind);
        }
        if (member.isPresent() && kind != Kind.A_MEMBER_THE_CLAUSE_NEEDS) {
            throw new IllegalArgumentException("only a member the clause needs is named: " + kind);
        }
    }

    /** A read naming no member. */
    public ClauseRead(RuleKey at, Kind kind, RuleKey run) {
        this(at, kind, run, Optional.empty());
    }

    /**
     * The member a clause cannot be true without its container holding.
     *
     * @param lookedFor the place of the value whose value the container is to hold
     * @param asAKey    whether it is to hold it as a key, as a map holds what {@code Map.get} and
     *                  {@code Map.containsKey} look up, rather than as an element
     * @param valueIn   for a key of a map, the numbers the clause says the value under it is to be
     *                  one of, as a range; empty where it says nothing of the value found
     */
    public record Member(RuleKey lookedFor, boolean asAKey,
                         Optional<NumericDomain.Bounds> valueIn) {

        public Member {
            Objects.requireNonNull(lookedFor, "a member is looked for at some place");
            Objects.requireNonNull(valueIn, "the numbers the value is to be among, or none");
            if (valueIn.isPresent() && !asAKey) {
                throw new IllegalArgumentException("only a key of a map has a value under it");
            }
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
         * ({@code ElementsApart}). Of whether the clause wants the elements apart, wants them not
         * to be, or does not turn on it, this says nothing.
         */
        EACH_ELEMENTS_RUN,

        /**
         * The same read, of a call the clause cannot be true without: it is false wherever the
         * elements are not apart. A list or a set of one element is apart from nothing, so the
         * call is no reason for it to be refused.
         */
        ELEMENTS_THE_CLAUSE_NEEDS_APART,

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
