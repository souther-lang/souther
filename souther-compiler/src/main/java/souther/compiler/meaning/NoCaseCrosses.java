package souther.compiler.meaning;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.BitSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * A proof that a line at a remainder decides in none of the cases it is said for, made without
 * asking any of them.
 *
 * <p>A line decides in a case where a row on each side of it can stand in that case. A line that
 * reads one remainder, {@code (D mod k)} for some sum {@code D} of whole numbers, holds or fails at
 * a row by what {@code D mod k} is there, and so does every condition of a case that reads a
 * remainder of the same sum, at whatever offset. The remainder a row has is one of {@code k}
 * residues, and what is asked of a case is which residues of the one sum its conditions leave.
 *
 * <p><b>What is proved.</b> A case is two rows, one holding the line and one failing it, meeting
 * every condition the case chose. Each node of the cases says which pairs of residues two rows may
 * have and meet it: a condition, the pairs of residues it holds at; an {@code EachOf}, the pairs of
 * any alternative; a {@code Together}, the pairs every factor has, because its factors are chosen
 * one at a time and a pair meets all of them where it meets each. That is exact where the
 * conditions read only that sum's remainder, and it takes in more where they read anything else:
 * <ul>
 *     <li>a condition that is not a relation of this one remainder is met by every residue, and
 *     its denial is too — what is not read is not held against a row;</li>
 *     <li>the rows are not asked to be rows the way to the line lets through: that only takes
 *     rows away;</li>
 *     <li>two rows are any two rows, though a case meeting both may need them to agree in
 *     something that is not read.</li>
 * </ul>
 * Where no pair with the line on one side and not the other meets the cases, no row of any case is
 * on both sides, so the cases are left out of where the line decides.
 *
 * <p><b>Proved or not, and nothing between.</b> A line that is not a relation of one remainder by a
 * whole divisor, whole numbers it is a sum of, or a divisor too large to be told apart, is not
 * proved to decide nowhere, and whoever asks goes on and asks the cases as it would have.
 */
public final class NoCaseCrosses {

    /** Most residues a remainder is told apart in: a pair of them is one bit of a set. */
    private static final int MOST_RESIDUES = 64;

    private final Predicate<NumericTerm> wholeInItsUnit;
    private final Sum sum;
    private final int divisor;
    private final Map<DecidingCase.Cases, BitSet> worked = new IdentityHashMap<>();

    private NoCaseCrosses(Predicate<NumericTerm> wholeInItsUnit, Sum sum) {
        this.wholeInItsUnit = wholeInItsUnit;
        this.sum = sum;
        this.divisor = sum.divisor().intValueExact();
    }

    /**
     * Whether {@code said} holds no row on each side of {@code line}, proved.
     *
     * @param wholeInItsUnit whether a number is a whole number of its own unit on every row
     */
    public static boolean proves(Proposition.Compared line, DecidingCase said,
                                 Predicate<NumericTerm> wholeInItsUnit) {
        Optional<Sum> read = new Reading(wholeInItsUnit).sumOfTheLine(line);
        if (read.isEmpty()) {
            return false;
        }
        NoCaseCrosses proof = new NoCaseCrosses(wholeInItsUnit, read.get());
        Optional<Long> holding = proof.residuesWhere(line);
        if (holding.isEmpty()) {
            return false;
        }
        long all = proof.every();
        long failing = all & ~holding.get();
        BitSet pairs = proof.pairsOf(said.standsFor());
        for (int one = 0; one < proof.divisor; one++) {
            if ((holding.get() & (1L << one)) == 0) {
                continue;
            }
            for (int other = 0; other < proof.divisor; other++) {
                if ((failing & (1L << other)) != 0 && pairs.get(one * proof.divisor + other)) {
                    return false;
                }
            }
        }
        return true;
    }

    // ---- the sum a remainder is of ----

    /**
     * What a remainder is the remainder of, less what it is offset by: the sum of the numbers it
     * is a remainder of, each by its coefficient modulo the divisor.
     */
    private record Sum(Map<Quantity, BigInteger> weights, BigInteger divisor) {}

    /** A remainder as the offset it has from the residue of its sum: {@code (R + offset) mod k}. */
    private record Offset(Sum of, BigInteger offset) {}

    private record Reading(Predicate<NumericTerm> wholeInItsUnit) {

        Optional<Sum> sumOfTheLine(Proposition.Compared line) {
            return remainderOf(line).map(Offset::of);
        }

        /** The one remainder a relation is of, and what it is of, where it is no more than that. */
        Optional<Offset> remainderOf(Proposition.Compared compared) {
            if (!(compared.relation() instanceof Relation.Affine affine)
                    || affine.form().coefs().size() != 1) {
                return Optional.empty();
            }
            Map.Entry<Quantity, ExactRatio> only = affine.form().coefs().entrySet().iterator()
                    .next();
            if (!(only.getKey() instanceof Quantity.RemainderOfADividend remainder)
                    || whole(only.getValue()) == null || whole(affine.form().constant()) == null) {
                return Optional.empty();
            }
            return offsetOf(remainder);
        }

        private Optional<Offset> offsetOf(Quantity.RemainderOfADividend remainder) {
            BigInteger divisor = remainder.divisor();
            if (divisor.compareTo(BigInteger.valueOf(MOST_RESIDUES)) > 0) {
                return Optional.empty();
            }
            LinearForm<Quantity> dividend = remainder.dividend();
            BigInteger constant = whole(dividend.constant());
            if (constant == null) {
                return Optional.empty();
            }
            Map<Quantity, BigInteger> weights = new LinkedHashMap<>();
            for (Map.Entry<Quantity, ExactRatio> each : dividend.coefs().entrySet()) {
                BigInteger coefficient = whole(each.getValue());
                Quantity number = each.getKey();
                boolean aNumberOfTheInput = number instanceof DecisionAtom.OfTheInput
                        || number instanceof Quantity.OfABinding;
                if (coefficient == null || !aNumberOfTheInput
                        || !number.wholeOnEveryRow(wholeInItsUnit)) {
                    return Optional.empty();
                }
                BigInteger weight = coefficient.mod(divisor);
                if (weight.signum() != 0) {
                    weights.put(number, weight);
                }
            }
            return Optional.of(new Offset(new Sum(weights, divisor), constant.mod(divisor)));
        }
    }

    private static BigInteger whole(ExactRatio ratio) {
        return ratio.isWhole() && ratio.floor() instanceof ExactAnswer.Held<BigInteger>(var held)
                ? held : null;
    }

    // ---- residues, as the bits of a long ----

    private long every() {
        return divisor == 64 ? -1L : (1L << divisor) - 1;
    }

    /**
     * The residues of the sum at which {@code relation}, a relation of one remainder of it, holds;
     * not where it is a relation of anything else.
     */
    private Optional<Long> residuesWhere(Proposition.Compared relation) {
        Reading reading = new Reading(wholeInItsUnit);
        Optional<Offset> read = reading.remainderOf(relation);
        if (read.isEmpty() || !read.get().of().equals(sum)) {
            return Optional.empty();
        }
        Relation.Affine affine = (Relation.Affine) relation.relation();
        BigInteger constant = whole(affine.form().constant());
        BigInteger coefficient = whole(affine.form().coefs().values().iterator().next());
        long held = 0;
        for (int residue = 0; residue < divisor; residue++) {
            BigInteger remainder = read.get().offset().add(BigInteger.valueOf(residue))
                    .mod(sum.divisor());
            int sign = constant.add(coefficient.multiply(remainder)).signum();
            if (affine.proposition().holds(sign) == relation.holds()) {
                held |= 1L << residue;
            }
        }
        return Optional.of(held);
    }

    /**
     * The residues a row may have and meet {@code condition}: those it holds at where it is a
     * relation of the sum's remainder, and every residue where it is anything else. A denial of
     * what is not read is not read either, which is why a denial is a relation's own
     * {@link Proposition.Compared#holds} and no complement is taken here.
     */
    private long residuesOf(Proposition condition) {
        return switch (condition) {
            case Proposition.Always always -> always.holds() ? every() : 0;
            case Proposition.All every -> {
                long met = every();
                for (Proposition part : every.parts()) {
                    met &= residuesOf(part);
                }
                yield met;
            }
            case Proposition.Any some -> {
                long met = 0;
                for (Proposition part : some.parts()) {
                    met |= residuesOf(part);
                }
                yield met;
            }
            case Proposition.Compared compared -> residuesWhere(compared).orElse(every());
            default -> every();
        };
    }

    // ---- the pairs of residues two rows may have and meet one case ----

    private BitSet pairsOf(DecidingCase.Cases cases) {
        BitSet known = worked.get(cases);
        if (known != null) {
            return known;
        }
        BitSet out = switch (cases) {
            case DecidingCase.Cases.One one -> pairsWithin(residuesOf(one.condition()));
            case DecidingCase.Cases.EachOf each -> {
                BitSet any = new BitSet();
                for (DecidingCase.Cases alternative : each.alternatives()) {
                    any.or(pairsOf(alternative));
                }
                yield any;
            }
            case DecidingCase.Cases.Together together -> {
                BitSet both = pairsWithin(every());
                for (DecidingCase.Cases factor : together.factors()) {
                    both.and(pairsOf(factor));
                }
                yield both;
            }
            case DecidingCase.Cases.NotTakenApart _ -> pairsWithin(every());
        };
        worked.put(cases, out);
        return out;
    }

    /** The pairs of residues both of which are among {@code residues}. */
    private BitSet pairsWithin(long residues) {
        BitSet pairs = new BitSet();
        for (int one = 0; one < divisor; one++) {
            if ((residues & (1L << one)) == 0) {
                continue;
            }
            for (int other = 0; other < divisor; other++) {
                if ((residues & (1L << other)) != 0) {
                    pairs.set(one * divisor + other);
                }
            }
        }
        return pairs;
    }
}
