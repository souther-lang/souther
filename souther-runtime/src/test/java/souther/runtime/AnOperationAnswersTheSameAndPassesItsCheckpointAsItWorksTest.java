package souther.runtime;

import net.unit8.notation199x.pattern.PatternImage;
import net.unit8.notation199x.pattern.PatternMachine;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import net.unit8.notation199x.pattern.StringPattern;
import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Every operation an evaluated class calls with a checkpoint answers what the same operation answers
 * without one, passes the checkpoint at least once for each element or character it goes over, and
 * stops where the checkpoint throws, part of the way through.
 *
 * <p>The inputs are long enough that an operation which handed its walk to the host in one call
 * would pass the checkpoint a handful of times rather than thousands, so the second claim tells a
 * walk that passes from one that does not. The third is what an evaluation relies on: what the
 * checkpoint throws comes out of the operation as it is.
 */
class AnOperationAnswersTheSameAndPassesItsCheckpointAsItWorksTest {

    private static final int N = 10_000;

    private static final String TEXT = "a".repeat(N);
    private static final String WORDS = "ab ".repeat(N / 3);
    private static final List<Long> NUMBERS = numbers();
    private static final List<Tuple> ENTRIES = entries();

    /** A checkpoint that counts what is passed and throws once it has been passed {@code stopAt}
     *  times. */
    private static final class Counting implements WorkCheckpoint {

        private final long stopAt;
        long passed;

        Counting(long stopAt) {
            this.stopAt = stopAt;
        }

        @Override
        public void spend(long pieces) {
            passed += pieces;
            if (passed >= stopAt) {
                thrown = new Stopped();
                throw thrown;
            }
        }

        /** What this threw, so that what comes out of an operation can be held to being it; null
         *  until it throws. */
        @Nullable Stopped thrown;
    }

    private static final class Stopped extends RuntimeException {
        private static final long serialVersionUID = 1L;

        Stopped() {
            super(null, null, false, false);
        }
    }

    /** An operation, as a shipped class and an evaluated one each call it, and how much of its input
     *  it goes over at least. */
    private record Operation(String name, Supplier<Object> shipped, Function<WorkCheckpoint, Object> evaluated,
                             long goesOver) {}

    private static List<Operation> operations() {
        Predicate<String> anyAs = pattern("a*");
        BigDecimal wide = new BigDecimal(BigInteger.TEN.pow(N));
        Rational third = Rational.of(BigInteger.ONE, BigInteger.valueOf(3));
        Rational apart = Rational.of(new BigDecimal(BigInteger.ONE, -N));
        Fn none = args -> false;
        List<Operation> ops = new ArrayList<>();
        ops.add(new Operation("String.length", () -> Strings.length(TEXT), c -> Strings.length(TEXT, c), N));
        ops.add(new Operation("String.compare", () -> Strings.compare(TEXT, TEXT + "b"),
                c -> Strings.compare(TEXT, TEXT + "b", c), N));
        ops.add(new Operation("String.contains", () -> TEXT.contains("b"),
                c -> Strings.contains(TEXT, "b", c), N));
        ops.add(new Operation("String.startsWith", () -> TEXT.startsWith(TEXT),
                c -> Strings.startsWith(TEXT, TEXT, c), N));
        ops.add(new Operation("String.endsWith", () -> TEXT.endsWith(TEXT),
                c -> Strings.endsWith(TEXT, TEXT, c), N));
        ops.add(new Operation("String.split", () -> Strings.split(WORDS, " "),
                c -> Strings.split(WORDS, " ", c), WORDS.length()));
        ops.add(new Operation("String.append", () -> Strings.append(TEXT, TEXT),
                c -> Strings.append(TEXT, TEXT, c), 2L * N));
        ops.add(new Operation("String.join", () -> Strings.join(List.of(TEXT, TEXT), ","),
                c -> Strings.join(List.of(TEXT, TEXT), ",", c), 2L * N));
        ops.add(new Operation("String.replace", () -> Strings.replace(TEXT, "a", "b"),
                c -> Strings.replace(TEXT, "a", "b", c), N));
        ops.add(new Operation("String.trim", () -> Strings.trim(" ".repeat(N) + "a"),
                c -> Strings.trim(" ".repeat(N) + "a", c), N));
        ops.add(new Operation("String.words", () -> Strings.words(WORDS), c -> Strings.words(WORDS, c),
                WORDS.length()));
        ops.add(new Operation("String.characters", () -> Strings.characters(TEXT),
                c -> Strings.characters(TEXT, c), N));
        ops.add(new Operation("String.codePoints", () -> Strings.codePoints(TEXT),
                c -> Strings.codePoints(TEXT, c), N));
        ops.add(new Operation("String.toInt", () -> Strings.toInt("0".repeat(N) + "7"),
                c -> Strings.toInt("0".repeat(N) + "7", c), N));
        ops.add(new Operation("String.toDecimal", () -> Strings.toDecimal("1" + "0".repeat(N)),
                c -> Strings.toDecimal("1" + "0".repeat(N), c), N));
        ops.add(new Operation("String.reverse", () -> Strings.reverse(TEXT), c -> Strings.reverse(TEXT, c), N));
        ops.add(new Operation("String.repeat", () -> Strings.repeat("ab", N), c -> Strings.repeat("ab", N, c), N));
        ops.add(new Operation("String.lines", () -> Strings.lines("a\r\n".repeat(N / 3)),
                c -> Strings.lines("a\r\n".repeat(N / 3), c), N / 3));
        ops.add(new Operation("String.padLeft", () -> Strings.padLeft("a", N, "b"),
                c -> Strings.padLeft("a", N, "b", c), N));
        ops.add(new Operation("String.slice", () -> Strings.slice(TEXT, N - 1, N),
                c -> Strings.slice(TEXT, N - 1, N, c), N));
        ops.add(new Operation("String.lowercase", () -> Strings.lowercase("A".repeat(N)),
                c -> Strings.lowercase("A".repeat(N), c), N));
        ops.add(new Operation("String.uppercase", () -> Strings.uppercase(TEXT), c -> Strings.uppercase(TEXT, c), N));
        ops.add(new Operation("String.admission", () -> Strings.admission(TEXT),
                c -> Strings.admission(TEXT, c), N));
        ops.add(new Operation("String.fromDecimal", () -> Strings.fromDecimal(wide),
                c -> Strings.fromDecimal(wide, c), N / 19));
        ops.add(new Operation("String.matches", () -> anyAs.test(TEXT),
                c -> Patterns.matches(anyAs, TEXT, c), N));
        ops.add(new Operation("Values.equal of texts", () -> Values.equal(TEXT, new String(TEXT)),
                c -> Values.equal(TEXT, new String(TEXT), c), N));
        // Another list holding the same elements, so the two are compared element by element and not
        // found to be one list.
        ops.add(new Operation("Values.equal of lists", () -> Values.equal(NUMBERS, new ArrayList<>(NUMBERS)),
                c -> Values.equal(NUMBERS, new ArrayList<>(NUMBERS), c), N));
        ops.add(new Operation("Values.hash of a list", () -> Values.hash(NUMBERS), c -> Values.hash(NUMBERS, c), N));
        ops.add(new Operation("List.reverse", () -> Lists.reverse(NUMBERS), c -> Lists.reverse(NUMBERS, c), N));
        ops.add(new Operation("List.sort", () -> Lists.sort(NUMBERS), c -> Lists.sort(NUMBERS, c), N));
        ops.add(new Operation("List.sort by text", () -> Lists.sort(Strings.ordering(), List.of(TEXT, "b", TEXT)),
                c -> Lists.sort(Strings.ordering(c), List.of(TEXT, "b", TEXT), c), N));
        ops.add(new Operation("List.max", () -> Lists.max(NUMBERS), c -> Lists.max(NUMBERS, c), N));
        ops.add(new Operation("List.rangeInclusive", () -> Lists.rangeInclusive(1, N),
                c -> Lists.rangeInclusive(1, N, c), N));
        ops.add(new Operation("List.sum", () -> Lists.sumInt(NUMBERS), c -> Lists.sumInt(NUMBERS, c), N));
        ops.add(new Operation("List.concat", () -> Lists.concat(NUMBERS, NUMBERS),
                c -> Lists.concat(NUMBERS, NUMBERS, c), N));
        ops.add(new Operation("List.find", () -> Lists.find(none, NUMBERS), c -> Lists.find(none, NUMBERS, c), N));
        ops.add(new Operation("Map.fromList", () -> Maps.fromList(ENTRIES), c -> Maps.fromList(ENTRIES, c), N));
        ops.add(new Operation("Map.toList", () -> Maps.toList(Maps.fromList(ENTRIES)),
                c -> Maps.toList(Maps.fromList(ENTRIES), c), N));
        ops.add(new Operation("Set.fromList", () -> Sets.fromList(NUMBERS), c -> Sets.fromList(NUMBERS, c), N));
        ops.add(new Operation("Set.union", () -> Sets.union(Sets.fromList(NUMBERS), Sets.fromList(List.of(-1L))),
                c -> Sets.union(Sets.fromList(NUMBERS), Sets.fromList(List.of(-1L)), c), N));
        ops.add(new Operation("Set.difference", () -> Sets.difference(Sets.fromList(NUMBERS), Sets.singleton(1L)),
                c -> Sets.difference(Sets.fromList(NUMBERS), Sets.singleton(1L), c), N));
        ops.add(new Operation("Decimal.multiply", () -> DecimalMath.multiply(wide, wide),
                // Each factor is ten thousand digits, over five hundred words of sixty-four bits, and
                // the schoolbook product of the two is what is paid.
                c -> DecimalMath.multiply(wide, wide, c), (long) (N / 20) * (N / 20)));
        ops.add(new Operation("Decimal.round", () -> DecimalMath.round(N, new HALF_UP(), BigDecimal.ONE),
                c -> DecimalMath.round(N, new HALF_UP(), BigDecimal.ONE, c), N / 19));
        ops.add(new Operation("Rational.add across a gap", () -> RationalMath.add(apart, third),
                c -> RationalMath.add(apart, third, c), N / 19));
        return ops;
    }

    @Test
    void anOperationAnswersWithACheckpointWhatItAnswersWithout() {
        for (Operation op : operations()) {
            Counting all = new Counting(Long.MAX_VALUE);
            assertTrue(Values.equal(op.shipped().get(), op.evaluated().apply(all)), op.name());
        }
    }

    @Test
    void anOperationPassesItsCheckpointForWhatItGoesOver() {
        for (Operation op : operations()) {
            Counting all = new Counting(Long.MAX_VALUE);
            assertTrue(Values.equal(op.shipped().get(), op.evaluated().apply(all)), op.name());
            assertTrue(all.passed >= op.goesOver(),
                    op.name() + " passed " + all.passed + " for " + op.goesOver() + " it goes over");
        }
    }

    @Test
    void anOperationStopsWhereItsCheckpointThrows() {
        for (Operation op : operations()) {
            Counting stopping = new Counting(op.goesOver() / 2 + 1);
            Stopped out = assertThrows(Stopped.class, () -> op.evaluated().apply(stopping), op.name());
            assertSame(stopping.thrown, out, op.name());
        }
    }

    /** A checkpoint nobody holds passes nothing and is what a shipped class's entry hands in, so the
     *  two entries are one body. */
    @Test
    void theCheckpointNobodyHoldsChangesNothing() {
        for (Operation op : operations()) {
            assertTrue(Values.equal(op.shipped().get(), op.evaluated().apply(WorkCheckpoint.NONE)), op.name());
        }
    }

    private static Predicate<String> pattern(String written) {
        if (!(PatternParser.read(written) instanceof PatternRead.Read(var meaning))) {
            fail("the pattern reads: " + written);
            throw new AssertionError();
        }
        if (!(PatternMachine.of(meaning).image() instanceof PatternImage.Written(var image))) {
            fail("the pattern's machine is written: " + written);
            throw new AssertionError();
        }
        return StringPattern.of(image);
    }

    private static List<Long> numbers() {
        List<Long> out = new ArrayList<>();
        for (long i = N; i > 0; i--) {
            out.add(i);
        }
        return List.copyOf(out);
    }

    private static List<Tuple> entries() {
        Map<Long, Long> pairs = new LinkedHashMap<>();
        for (long i = 0; i < N; i++) {
            pairs.put(i, i * 2);
        }
        List<Tuple> out = new ArrayList<>();
        pairs.forEach((k, v) -> out.add(Tuple.of(k, v)));
        return out;
    }
}
