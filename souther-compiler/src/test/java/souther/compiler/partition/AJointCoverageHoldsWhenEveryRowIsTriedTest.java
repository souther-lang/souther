package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.UndividedByARelation.WholeEnds;
import souther.test.Nightly;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Choosing the pivot for statements that move the form by a number the run chooses is a claim
 * about every row of the other numbers and about every number the way's own statements of it
 * leave, and it is tried against every one. Whatever {@link RemainderCoverage#proveJointly} shows
 * is checked by working it out: for every number from {@code low} to {@code high} that the
 * statements of the number alone allow, and every value of the numbers the claim is about, some
 * value of the pivot meets every statement with the form moved by that number, the form and each
 * move inside the type.
 *
 * <p>What the proof does not show is not asked: it is allowed to fall short, and the claim is
 * that what it shows is so. The ranges of the number go past twice the divisor, so that the
 * numbers the proof does not try, those between its two ends, are tried here.
 *
 * <p>Nightly, for what it costs: tens of thousands of instances, each worked out over every row.
 * Each way of the proof showing too much that a sweep found is a case of
 * {@link AJointProofAsksEveryNumberItSpeaksForTest}, which asks it of one instance at every change;
 * this finds the ones nobody has thought of yet, and finding one by morning is soon enough.
 */
@Nightly
class AJointCoverageHoldsWhenEveryRowIsTriedTest {

    private static final int INSTANCES = 40000;

    @Test
    void whateverTheJointProofShowsIsSoOverEveryRowAndEveryNumber() {
        Random random = new Random(3271);
        int shown = 0;
        int wide = 0;
        for (int i = 0; i < INSTANCES; i++) {
            Instance instance = Instance.random(random);
            if (instance.prove().isPresent()) {
                shown++;
                if (instance.high() - instance.low() >= 2L * instance.divisor().intValue()) {
                    wide++;
                }
                assertTrue(instance.holdsAtEveryRowAndNumber(), instance.toString());
            }
        }
        assertTrue(shown > INSTANCES / 50, "shown only " + shown);
        assertTrue(wide > shown / 10, "shown over a wide range only " + wide);
    }

    /**
     * What lets the proof leave the numbers between its two ends unasked: the numbers at which
     * {@link RemainderCoverage#prove} holds, with every statement moved by a whole multiple of the
     * number as well as by a constant, are the numbers between two, and none has a gap. Tried
     * with the narrowings the run may state of the form, which bound it from either side.
     */
    @Test
    void theNumbersAtWhichTheProofHoldsHaveNoGap() {
        Random random = new Random(3273);
        int mixed = 0;
        int asked = INSTANCES / 5;
        for (int i = 0; i < asked; i++) {
            Instance instance = Instance.random(random);
            List<TakenConstraint> narrowing = narrowingsOf(random, instance);
            boolean[] holds = new boolean[121];
            int held = 0;
            for (int n = -40; n <= 80; n++) {
                List<BigInteger> moves = new ArrayList<>();
                for (RemainderCoverage.Moved each : instance.statements()) {
                    moves.add(each.shift().add(each.onTheNumber().multiply(big(n))));
                }
                holds[n + 40] = RemainderCoverage.prove(instance.pivot(), instance.pivotEnds(),
                        instance.others(), instance.dividend(), moves, instance.divisor(),
                        narrowing, instance.least(), instance.greatest()).isPresent();
                held += holds[n + 40] ? 1 : 0;
            }
            int first = -1;
            int last = -1;
            for (int n = 0; n < holds.length; n++) {
                if (holds[n]) {
                    first = first < 0 ? n : first;
                    last = n;
                }
            }
            for (int n = first; n <= last && first >= 0; n++) {
                assertTrue(holds[n], "a gap at " + (n - 40) + ": " + instance + " " + narrowing);
            }
            mixed += held > 0 && held < holds.length ? 1 : 0;
        }
        assertTrue(mixed > asked / 20, "the proof held at some numbers and not others only "
                + mixed);
    }

    private static List<TakenConstraint> narrowingsOf(Random random, Instance instance) {
        List<NumericTerm> all = new ArrayList<>(instance.dividend().coefs().keySet());
        List<TakenConstraint> narrowing = new ArrayList<>();
        for (int i = random.nextInt(4); i > 0; i--) {
            Map<NumericTerm, ExactRatio> form = new LinkedHashMap<>();
            for (NumericTerm each : all) {
                if (random.nextBoolean()) {
                    form.put(each, ExactRatio.of(random.nextBoolean() ? 1 : -1));
                }
            }
            if (!form.isEmpty()) {
                narrowing.add(new TakenConstraint.Affine(new LinearForm<>(
                        ExactRatio.of(random.nextInt(41) - 20), form),
                        random.nextBoolean() ? Rel.LE : Rel.GE));
            }
        }
        return narrowing;
    }

    /** One form over a pivot and a few numbers, moved by a number lying from {@code low} to
     *  {@code high}. */
    private record Instance(NumericTerm pivot, WholeEnds pivotEnds,
                            Map<NumericTerm, RemainderCoverage.Other> others,
                            LinearForm<NumericTerm> dividend,
                            List<RemainderCoverage.Moved> statements,
                            List<RemainderCoverage.Moved> ofTheNumber, BigInteger divisor,
                            BigInteger least, BigInteger greatest, long low, long high) {

        static Instance random(Random random) {
            NumericTerm pivot = term("p");
            Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
            coefs.put(pivot, ExactRatio.of(random.nextBoolean() ? 1 : -1));
            Map<NumericTerm, RemainderCoverage.Other> others = new LinkedHashMap<>();
            for (int i = random.nextInt(3); i > 0; i--) {
                NumericTerm each = term("u" + others.size());
                coefs.put(each, ExactRatio.of(random.nextBoolean() ? 1 : -1));
                int low = random.nextInt(7) - 4;
                others.put(each, new RemainderCoverage.Other(
                        new WholeEnds(big(low), big(low + random.nextInt(9))), false));
            }
            int divisor = new int[] {2, 3, 4, 5, 7}[random.nextInt(5)];
            List<RemainderCoverage.Moved> statements = new ArrayList<>();
            for (int i = 1 + random.nextInt(3); i > 0; i--) {
                statements.add(new RemainderCoverage.Moved(big(random.nextInt(7) - 3),
                        big(random.nextInt(5) - 2), someOf(random, divisor, 2)));
            }
            List<RemainderCoverage.Moved> ofTheNumber = new ArrayList<>();
            if (random.nextBoolean()) {
                ofTheNumber.add(new RemainderCoverage.Moved(big(random.nextInt(3)),
                        BigInteger.ONE, someOf(random, divisor, 1)));
            }
            int low = random.nextInt(6) - 5;
            long from = random.nextInt(4);
            return new Instance(pivot, new WholeEnds(big(low), big(low + random.nextInt(25))),
                    others, new LinearForm<>(ExactRatio.ZERO, coefs), statements, ofTheNumber,
                    big(divisor), big(-30 + random.nextInt(8)), big(12 + random.nextInt(19)),
                    from, from + random.nextInt(16));
        }

        /** Some remainders, each kept with one chance in {@code of} out of three. */
        private static Set<Integer> someOf(Random random, int divisor, int of) {
            Set<Integer> allowed = new LinkedHashSet<>();
            for (int r = 0; r < divisor; r++) {
                if (random.nextInt(3) < of) {
                    allowed.add(r);
                }
            }
            if (allowed.isEmpty()) {
                allowed.add(random.nextInt(divisor));
            }
            return allowed;
        }

        Optional<RemainderCoverage.Proof> prove() {
            return RemainderCoverage.proveJointly(pivot, pivotEnds, others, dividend, statements,
                    ofTheNumber, divisor, List.of(), least, greatest, low, high);
        }

        /** The claim, worked out: every number the statements of it allow, every row. */
        boolean holdsAtEveryRowAndNumber() {
            for (long n = low; n <= high; n++) {
                if (allowsTheNumber(n) && !everyRow(new ArrayList<>(others.keySet()), 0, new LinkedHashMap<>(),
                                n)) {
                    return false;
                }
            }
            return true;
        }

        private boolean everyRow(List<NumericTerm> universal, int at,
                                 Map<NumericTerm, BigInteger> row, long n) {
            if (at < universal.size()) {
                NumericTerm each = universal.get(at);
                WholeEnds ends = others.get(each).ends();
                for (BigInteger v = ends.low(); v.compareTo(ends.high()) <= 0;
                     v = v.add(BigInteger.ONE)) {
                    row.put(each, v);
                    if (!everyRow(universal, at + 1, row, n)) {
                        return false;
                    }
                }
                row.remove(each);
                return true;
            }
            for (BigInteger p = pivotEnds.low(); p.compareTo(pivotEnds.high()) <= 0;
                 p = p.add(BigInteger.ONE)) {
                Map<NumericTerm, BigInteger> held = new LinkedHashMap<>(row);
                held.put(pivot, p);
                if (meetsEvery(sum(held), n)) {
                    return true;
                }
            }
            return false;
        }

        private boolean allowsTheNumber(long n) {
            for (RemainderCoverage.Moved each : ofTheNumber) {
                BigInteger moved = each.shift().add(each.onTheNumber().multiply(big(n)));
                if (!each.allowed().contains(moved.mod(divisor).intValue())) {
                    return false;
                }
            }
            return true;
        }

        private boolean meetsEvery(BigInteger form, long n) {
            for (RemainderCoverage.Moved each : statements) {
                BigInteger moved = form.add(each.shift()).add(
                        each.onTheNumber().multiply(big(n)));
                if (moved.compareTo(least) < 0 || moved.compareTo(greatest) > 0
                        || !each.allowed().contains(moved.mod(divisor).intValue())) {
                    return false;
                }
            }
            return true;
        }

        private BigInteger sum(Map<NumericTerm, BigInteger> at) {
            BigInteger out = BigInteger.ZERO;
            for (Map.Entry<NumericTerm, ExactRatio> each : dividend.coefs().entrySet()) {
                out = out.add(each.getValue().wholeOrNull()
                        .multiply(at.getOrDefault(each.getKey(), BigInteger.ZERO)));
            }
            return out;
        }

        @Override
        public String toString() {
            return "pivot " + pivotEnds + " form " + dividend.coefs() + " statements "
                    + statements + " of the number " + ofTheNumber + " mod " + divisor
                    + " others " + others + " in [" + least + ", " + greatest + "] n in " + low
                    + ".." + high;
        }
    }

    private static NumericTerm term(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static BigInteger big(long value) {
        return BigInteger.valueOf(value);
    }
}
