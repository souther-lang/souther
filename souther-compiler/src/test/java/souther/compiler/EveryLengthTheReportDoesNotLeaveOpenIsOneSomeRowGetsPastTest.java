package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a report classes the strings of a position whose length the way holds against a number, it
 * classes only lengths some row gets a run past, and leaves the rest open.
 *
 * <p>Asked of an independent run: every string of the position up to a length, with every value of
 * the number its declarations leave, is worked out by the rules of the language — an addition
 * stops a run where it passes the greatest {@code Int} — and the lengths at which some row reaches
 * the equality are the ones the report is held to. The report is read as a person reads it: the
 * open lengths it says, and whether it classes the strings at all.
 *
 * <p>What a model is built from varies each thing a proof that a row reaches the equality stands
 * on, one at a time: the strings the position admits (a single length, a range, lengths with a
 * gap, no bound), the numbers the declarations leave the number (at the greatest, at both ends,
 * about nought), the guard that holds the length against it, and an operation on the number
 * before that guard.
 */
class EveryLengthTheReportDoesNotLeaveOpenIsOneSomeRowGetsPastTest {

    private static final BigInteger GREATEST = BigInteger.valueOf(Long.MAX_VALUE);

    private static final BigInteger LEAST = BigInteger.valueOf(Long.MIN_VALUE);

    /** The longest string the run enumerates; longer ones are not asked. */
    private static final int LONGEST = 6;

    private static final List<String> POSITIONS = List.of("[ab]{3}", "[ab]{0,2}", "[ab]{1,3}",
            "([ab][ab])+", "[ab]+");

    /** The numbers the declarations leave the number: least and greatest. */
    private static final List<BigInteger[]> NUMBERS = List.of(
            new BigInteger[] {GREATEST.subtract(BigInteger.TWO), GREATEST},
            new BigInteger[] {GREATEST.subtract(BigInteger.valueOf(3)),
                    GREATEST.subtract(BigInteger.ONE)},
            new BigInteger[] {BigInteger.valueOf(-2), BigInteger.TWO},
            new BigInteger[] {GREATEST.subtract(BigInteger.ONE), GREATEST});

    /** The comparisons the length and the number are held to: relation and bound. */
    private static final List<String[]> GUARDS = List.of(new String[] {">", "0"},
            new String[] {">", GREATEST.subtract(BigInteger.TWO).toString()},
            new String[] {">", GREATEST.subtract(BigInteger.ONE).toString()},
            new String[] {"<=", "1"});

    private static final List<Boolean> BEFORE = List.of(false, true);

    record Shape(String position, BigInteger[] number, String[] guard, boolean before) {

        String source() {
            return """
                    module example.equal

                    data A = String
                        invariant String.matches("[ab]+", value)

                    data B = String
                        invariant String.matches("%s", value)

                    data N = Int
                        invariant value >= %s && value <= %s

                    behavior f : (a: A, b: B, n: N) -> Bool

                    let f (a, b, n) = {
                        %s
                        guard String.length(b.value) + n.value %s %s else false
                        a.value == b.value && String.length(a.value) > 1
                    }
                    """.formatted(position, number[0], number[1],
                    before ? "guard n.value + 1 > 0 else false" : "", guard[0], guard[1]);
        }

        /** The lengths of the strings the position admits, up to the longest asked. */
        Set<Integer> admitted() {
            Pattern pattern = Pattern.compile(position);
            Set<Integer> out = new TreeSet<>();
            for (int length = 0; length <= LONGEST; length++) {
                for (int bits = 0; bits < 1 << length; bits++) {
                    StringBuilder text = new StringBuilder();
                    for (int at = 0; at < length; at++) {
                        text.append((bits >> at & 1) == 0 ? 'a' : 'b');
                    }
                    if (pattern.matcher(text).matches()) {
                        out.add(length);
                    }
                }
            }
            return out;
        }

        /** The lengths at which some value of the number gets a run to the equality. */
        Set<Integer> reached() {
            Set<Integer> out = new TreeSet<>();
            for (int length : admitted()) {
                for (BigInteger n = number[0]; n.compareTo(number[1]) <= 0;
                        n = n.add(BigInteger.ONE)) {
                    if (before && (n.add(BigInteger.ONE).compareTo(GREATEST) > 0
                            || n.add(BigInteger.ONE).signum() <= 0)) {
                        continue;
                    }
                    BigInteger sum = n.add(BigInteger.valueOf(length));
                    if (sum.compareTo(GREATEST) > 0 || sum.compareTo(LEAST) < 0) {
                        continue;
                    }
                    int order = sum.compareTo(new BigInteger(guard[1]));
                    if (guard[0].equals(">") ? order > 0 : order <= 0) {
                        out.add(length);
                    }
                }
            }
            return out;
        }

        @Override
        public String toString() {
            return source();
        }
    }

    static List<Shape> shapes() {
        List<Shape> out = new ArrayList<>();
        for (String position : POSITIONS) {
            for (BigInteger[] number : NUMBERS) {
                for (String[] guard : GUARDS) {
                    for (boolean before : BEFORE) {
                        out.add(new Shape(position, number, guard, before));
                    }
                }
            }
        }
        return out;
    }

    /** The lengths the report leaves open, up to the longest asked, as a person reads them. */
    private static Set<Integer> openIn(String json) {
        Set<Integer> out = new TreeSet<>();
        Matcher each = Pattern.compile("\"leftOpen\"\\s*:\\s*\\{([^}]*)\\}").matcher(json);
        while (each.find()) {
            String open = each.group(1);
            Matcher longer = Pattern.compile("\"longerThan\"\\s*:\\s*(\\d+)").matcher(open);
            Matcher shorter = Pattern.compile("\"shorterThan\"\\s*:\\s*(\\d+)").matcher(open);
            boolean everything = open.matches("(?s).*\"atAnyLength\"\\s*:\\s*true.*");
            for (int length = 0; length <= LONGEST; length++) {
                if (everything
                        || (longer.find(0) && length > Integer.parseInt(longer.group(1)))
                        || (shorter.find(0) && length < Integer.parseInt(shorter.group(1)))) {
                    out.add(length);
                }
            }
        }
        return out;
    }

    static void holds(Shape shape) {
        Compilation compilation = Compilation.ofSource(shape.source(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "compiles: " + shape);
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("f");
        Set<String> classed = new TreeSet<>();
        List<String> sayings = new ArrayList<>();
        evidence.axes().forEach(axis -> {
            classed.add(axis.path());
            sayings.addAll(axis.classes());
        });
        Set<Integer> reached = shape.reached();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        if (reached.isEmpty()) {
            // No row gets to the equality, so no class says what a value is beside it.
            assertTrue(sayings.stream().noneMatch(saying ->
                            saying.contains(" can be ") || saying.contains(" is never ")),
                    "no row gets to the equality, so no class says what a string is beside"
                            + " the other: " + sayings + shape);
            return;
        }
        if (!classed.contains("b")) {
            return;
        }
        Set<Integer> open = openIn(json);
        for (int length : shape.admitted()) {
            if (length == 0) {
                // The other string has at least one code point, so the empty string is never
                // equal to it whichever row is run: the language says so, and no row is asked.
                continue;
            }
            assertTrue(open.contains(length) || reached.contains(length),
                    "length " + length + " is classed and no row gets a run past at it; open "
                            + open + ", reached " + reached + shape);
        }
    }

    /** Every tenth shape, which is quick enough to ask on every change. */
    @Test
    void aSampleOfTheShapesClassesOnlyLengthsSomeRowGetsPast() {
        List<Shape> all = shapes();
        for (int at = 0; at < all.size(); at += 10) {
            holds(all.get(at));
        }
    }

}
