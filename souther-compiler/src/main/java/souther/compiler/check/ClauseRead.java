package souther.compiler.check;

import java.util.List;
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
 * @param run  for {@link Kind#EACH_ELEMENTS_RUN}, the fields of an element it reads, one after
 *             another; empty for every other kind
 */
public record ClauseRead(RuleKey at, Kind kind, List<String> run) {

    public ClauseRead {
        Objects.requireNonNull(at, "a clause reads somewhere");
        Objects.requireNonNull(kind, "a clause reads something of where it reads");
        run = List.copyOf(run);
        if (kind != Kind.EACH_ELEMENTS_RUN && !run.isEmpty()) {
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
        EACH_ELEMENTS_RUN
    }
}
