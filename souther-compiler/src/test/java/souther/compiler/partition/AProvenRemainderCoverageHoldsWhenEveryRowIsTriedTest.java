package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.WholeEnds;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A coverage of a remainder is a claim about every row, and it is tried against every row. For
 * each instance of a form over a few numbers with a few narrowings, in a type small enough to
 * walk, whatever {@link RemainderCoverage#prove} shows is checked by working the claim out: for
 * every value of the numbers the claim is about that the narrowings of those numbers alone leave,
 * and every remainder, some value of the pivot puts the form there with the numbers chosen at
 * nought, every narrowing that names a number chosen holding, and the form moved by each of the
 * statements inside the type.
 *
 * <p>What the proof does not show is not asked: it is allowed to fall short, and the claim is
 * that what it shows is so.
 */
class AProvenRemainderCoverageHoldsWhenEveryRowIsTriedTest {

    private static final int INSTANCES = 60000;

    @Test
    void whateverTheProofShowsIsSoOverEveryRow() {
        Random random = new Random(3264);
        int shown = 0;
        for (int i = 0; i < INSTANCES; i++) {
            Instance instance = Instance.random(random);
            Optional<RemainderCoverage.Proof> proof = instance.prove();
            if (proof.isPresent()) {
                shown++;
                assertTrue(instance.holdsAtEveryRow(), instance.toString());
            }
        }
        // A proof that shows nothing is true of everything.
        assertTrue(shown > INSTANCES / 50, "shown only " + shown);
    }

    /** One form, with the numbers it is over and what the run narrows. */
    private record Instance(NumericTerm pivot, WholeEnds pivotEnds,
                            Map<NumericTerm, RemainderCoverage.Other> others,
                            LinearForm<NumericTerm> dividend, List<BigInteger> moves,
                            BigInteger divisor, List<TakenConstraint> narrowing,
                            BigInteger least, BigInteger greatest) {

        static Instance random(Random random) {
            NumericTerm pivot = term("p");
            List<NumericTerm> universal = new ArrayList<>();
            for (int i = random.nextInt(3); i > 0; i--) {
                universal.add(term("u" + universal.size()));
            }
            NumericTerm nought = random.nextInt(3) == 0 ? term("n") : null;
            Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
            int[] weights = {1, -1, 2, -2, 3};
            coefs.put(pivot, ExactRatio.of(weights[random.nextInt(weights.length)]));
            Map<NumericTerm, RemainderCoverage.Other> others = new LinkedHashMap<>();
            for (NumericTerm each : universal) {
                coefs.put(each, ExactRatio.of(weights[random.nextInt(weights.length)]));
                int low = random.nextInt(7) - 4;
                others.put(each, new RemainderCoverage.Other(
                        new WholeEnds(big(low), big(low + random.nextInt(9))), false));
            }
            if (nought != null) {
                coefs.put(nought, ExactRatio.of(weights[random.nextInt(weights.length)]));
                int low = random.nextInt(5) - 3;
                others.put(nought, new RemainderCoverage.Other(
                        new WholeEnds(big(low), big(low + random.nextInt(6))), true));
            }
            List<BigInteger> moves = new ArrayList<>();
            for (int i = 1 + random.nextInt(2); i > 0; i--) {
                moves.add(big(random.nextInt(7)));
            }
            int low = random.nextInt(6) - 5;
            WholeEnds pivotEnds = new WholeEnds(big(low), big(low + random.nextInt(15)));
            List<NumericTerm> all = new ArrayList<>(coefs.keySet());
            List<TakenConstraint> narrowing = new ArrayList<>();
            for (int i = random.nextInt(5); i > 0; i--) {
                Map<NumericTerm, ExactRatio> form = new LinkedHashMap<>();
                for (NumericTerm each : all) {
                    if (random.nextBoolean()) {
                        form.put(each, ExactRatio.of(random.nextBoolean() ? 1 : -1));
                    }
                }
                if (form.isEmpty()) {
                    continue;
                }
                // Often the form is the dividend's own, as the program's addition makes it, or
                // what of it the numbers the claim is about make.
                int made = random.nextInt(3);
                if (made > 0) {
                    form = new LinkedHashMap<>();
                    int sign = random.nextBoolean() ? 1 : -1;
                    for (Map.Entry<NumericTerm, ExactRatio> each : coefs.entrySet()) {
                        boolean aboutTheClaim = others.containsKey(each.getKey())
                                && !others.get(each.getKey()).chosenAtNought();
                        if (made == 1 || aboutTheClaim) {
                            form.put(each.getKey(), each.getValue().times(ExactRatio.of(sign))
                                    .orNull());
                        }
                    }
                    if (form.isEmpty()) {
                        continue;
                    }
                }
                narrowing.add(new TakenConstraint.Affine(new LinearForm<>(
                        ExactRatio.of(random.nextInt(31) - 15), form),
                        random.nextBoolean() ? Rel.LE : Rel.GE));
            }
            return new Instance(pivot, pivotEnds, others,
                    new LinearForm<>(ExactRatio.ZERO, coefs), moves,
                    big(new int[] {2, 3, 4, 5, 7}[random.nextInt(5)]), narrowing,
                    big(-12 + random.nextInt(8)), big(4 + random.nextInt(9)));
        }

        Optional<RemainderCoverage.Proof> prove() {
            return RemainderCoverage.prove(pivot, pivotEnds, others, dividend, moves, divisor,
                    narrowing, least, greatest);
        }

        /** The claim, worked out: every row of the numbers the claim is about, every remainder. */
        boolean holdsAtEveryRow() {
            List<NumericTerm> universal = others.entrySet().stream()
                    .filter(each -> !each.getValue().chosenAtNought()).map(Map.Entry::getKey)
                    .toList();
            return everyRow(universal, 0, new LinkedHashMap<>());
        }

        private boolean everyRow(List<NumericTerm> universal, int at,
                                 Map<NumericTerm, BigInteger> row) {
            if (at < universal.size()) {
                NumericTerm each = universal.get(at);
                WholeEnds ends = others.get(each).ends();
                for (BigInteger v = ends.low(); v.compareTo(ends.high()) <= 0;
                     v = v.add(BigInteger.ONE)) {
                    row.put(each, v);
                    if (!everyRow(universal, at + 1, row)) {
                        return false;
                    }
                }
                row.remove(each);
                return true;
            }
            // A row the narrowings of the numbers alone leave out is no row of the claim.
            Map<NumericTerm, BigInteger> chosen = new LinkedHashMap<>(row);
            others.forEach((term, other) -> {
                if (other.chosenAtNought()) {
                    chosen.put(term, BigInteger.ZERO);
                }
            });
            for (TakenConstraint each : narrowing) {
                if (each.terms().stream().noneMatch(term -> term.equals(pivot)
                        || (others.containsKey(term) && others.get(term).chosenAtNought()))
                        && !holds((TakenConstraint.Affine) each, chosen)) {
                    return true;
                }
            }
            for (int r = 0; r < divisor.intValue(); r++) {
                if (!somePivotPutsTheFormAt(r, chosen)) {
                    return false;
                }
            }
            return true;
        }

        private boolean somePivotPutsTheFormAt(int remainder, Map<NumericTerm, BigInteger> row) {
            BigInteger rest = moves.stream().reduce(BigInteger::min).orElseThrow();
            for (BigInteger p = pivotEnds.low(); p.compareTo(pivotEnds.high()) <= 0;
                 p = p.add(BigInteger.ONE)) {
                Map<NumericTerm, BigInteger> at = new LinkedHashMap<>(row);
                at.put(pivot, p);
                BigInteger form = sum(at);
                if (form.add(rest).mod(divisor).intValue() != remainder
                        || moves.stream().anyMatch(move -> form.add(move).compareTo(least) < 0
                                || form.add(move).compareTo(greatest) > 0)) {
                    continue;
                }
                boolean narrowed = true;
                for (TakenConstraint each : narrowing) {
                    boolean names = each.terms().stream().anyMatch(term -> term.equals(pivot)
                            || (others.containsKey(term) && others.get(term).chosenAtNought()));
                    narrowed &= !names || holds((TakenConstraint.Affine) each, at);
                }
                if (narrowed) {
                    return true;
                }
            }
            return false;
        }

        private BigInteger sum(Map<NumericTerm, BigInteger> at) {
            BigInteger out = BigInteger.ZERO;
            for (Map.Entry<NumericTerm, ExactRatio> each : dividend.coefs().entrySet()) {
                BigInteger value = at.getOrDefault(each.getKey(), BigInteger.ZERO);
                out = out.add(UndividedByARelation.wholeNumberOf(each.getValue())
                        .multiply(value));
            }
            return out;
        }

        private static boolean holds(TakenConstraint.Affine constraint,
                                     Map<NumericTerm, BigInteger> at) {
            BigInteger value = UndividedByARelation.wholeNumberOf(constraint.form().constant());
            for (Map.Entry<NumericTerm, ExactRatio> each : constraint.form().coefs().entrySet()) {
                value = value.add(UndividedByARelation.wholeNumberOf(each.getValue())
                        .multiply(at.getOrDefault(each.getKey(), BigInteger.ZERO)));
            }
            return constraint.rel() == Rel.LE ? value.signum() <= 0 : value.signum() >= 0;
        }

        @Override
        public String toString() {
            return "pivot " + pivotEnds + " form " + dividend.coefs() + " moves " + moves
                    + " mod " + divisor + " others " + others + " narrowing " + narrowing
                    + " in [" + least + ", " + greatest + "]";
        }
    }

    private static NumericTerm term(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static BigInteger big(long value) {
        return BigInteger.valueOf(value);
    }
}
