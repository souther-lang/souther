package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.Map;

/**
 * How much a position may hold, asked of the rules rather than read off them.
 *
 * <p>Every question here has one shape: settle the count at some number and see whether anything is
 * left. A rule removes a count in more ways than a bound written at the position — a length counted
 * under another spelling, a floor stated through a second field, an equality that names no end at all
 * — and reading the clauses for the shapes one reader thought of leaves the rest of them saying
 * nothing. The seeding already relates all of them, so the question goes there.
 *
 * <p>Yes wherever the reading fell short: a clause the seeding could not take in, a position nothing
 * counts, a reading that fell over. Unsupported information may leave more values in than there are
 * and may never leave fewer out — what these answers decide is that something cannot be built, and a
 * reader that guessed would refuse a type somebody can write.
 */
public final class OccurrenceCounts {

    /**
     * What a position no declaration wrote about leaves: every count.
     *
     * <p>A value a collection holds is one of these. There is no field for a record to have written a
     * rule about, so nothing here is narrowed by anything, and a reader that carried the collection's
     * own rules down to it would read a rule about how many there are as a rule about each one.
     */
    public static final OccurrenceCounts NOTHING_READ = new OccurrenceCounts(null);

    private final InvariantChecker.Seeded seeded;

    private OccurrenceCounts(InvariantChecker.Seeded seeded) {
        this.seeded = seeded;
    }

    /**
     * The counts {@code data}, declared as {@code named}, leaves its positions able to hold.
     *
     * <p>Seeded once and asked many times: filling a set from a finite element asks about every size
     * up to how many values the element has, and each of those is the same reading of the same
     * clauses.
     */
    public static OccurrenceCounts of(TypeSymbol named, Hir.Data data, Symbols symbols) {
        return of(named, data, symbols, _ -> false);
    }

    /**
     * The same, with the declarations {@code granted} names supposed to hold values.
     *
     * <p>Read this way by whatever is asking what would be true if some declaration had values. Its
     * rules are what say it has none — its own, and the ones under whatever it wraps — so supposing
     * it has a value is not reading it at all.
     */
    static OccurrenceCounts of(TypeSymbol named, Hir.Data data, Symbols symbols,
                                 java.util.function.Predicate<TypeSymbol> granted) {
        return new OccurrenceCounts(
                InvariantChecker.seedFields(named, data, symbols, java.util.Map.of(),
                        InvariantChecker.Reach.stoppingAt(granted)));
    }

    /** Whether the value at {@code path} may hold no more than {@code count}. */
    public boolean mayHoldAtMost(String path, long count) {
        return mayHold(path, count, NumericDomain.Rel.LE);
    }

    /** Whether the value at {@code path} may hold {@code count} and no other number. */
    public boolean mayHoldExactly(String path, long count) {
        return mayHold(path, count, NumericDomain.Rel.EQ);
    }

    /** Whether the value at {@code path} may hold {@code count} or more. */
    public boolean mayHoldAtLeast(String path, long count) {
        return mayHold(path, count, NumericDomain.Rel.GE);
    }

    /**
     * The fewest the value at {@code path} may hold, or none where the rules leave it open below.
     *
     * <p>A number and not an answer. What this is for is deciding which counts are worth telling
     * apart, and a reading that came back short of the floor keeps fewer of them than it might: the
     * counts it keeps still answer the questions asked at them, and the ones it drops make some other
     * answer wider than it needed to be. Nothing is refused on the strength of this — that is
     * {@link #mayHoldAtMost} and the others, which ask rather than read.
     */
    long leastHeldAt(String path) {
        if (seeded == null) {
            return 0;
        }
        String counted = seeded.held().get(path);
        return counted == null ? 0
                : CountDomain.leastFrom(seeded.numbers().boundsOf(counted).min());
    }

    private boolean mayHold(String path, long count, NumericDomain.Rel against) {
        if (seeded == null) {
            return true;
        }
        String counted = seeded.held().get(path);
        if (counted == null) {
            return true;   // nothing counts what is there, so no rule here is about how much it holds
        }
        NumericDomain.LinearForm from = NumericDomain.LinearForm.atom(counted)
                .minus(NumericDomain.LinearForm.constant(BigDecimal.valueOf(count)));
        return !seeded.numbers()
                .assume(from, against, Map.of(counted, Granularity.DISCRETE))
                .isBottom();
    }
}
