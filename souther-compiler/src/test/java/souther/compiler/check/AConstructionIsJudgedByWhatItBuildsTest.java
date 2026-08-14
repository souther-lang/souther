package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A construction is judged by the value it builds, not by the way it was written (issue #722).
 *
 * <p>Every source form that makes a value of a declared type is one node by the time anything reads
 * it, holding what each field is given (spec §invariant-discharge). So the spellings below are one
 * construction: a literal writing its fields, a literal spreading them from another value, one
 * spreading them from a sum whose cases share them, one spreading them from a field path, and the
 * arithmetic that builds a newtype from two of its own. Each is asked the same question about the
 * same values, and the answer is the same.
 *
 * <p>Both answers are held. A test that only showed the unguarded spellings warning would pass on a
 * check that had stopped discharging anything, and one that only showed the guarded spellings silent
 * would pass on a check that had stopped reading them.
 */
class AConstructionIsJudgedByWhatItBuildsTest {

    private static final String TYPES = """
            module demo

            data Common = { id: Int, n: Int }
            data A = { ...Common, a: Int }
            data B = { ...Common, b: Int }
            data S = A | B
            data Box = { inner: Common }

            data NonNeg = { id: Int, n: Int }
                invariant nonNeg = n >= 0

            data TooSmall
            """;

    /** The construction, reached with nothing known about what it is given. */
    private static String unguarded(String input, String body) {
        return TYPES + """

                behavior make : (%s) -> NonNeg
                    constructs NonNeg
                let make (x) = %s
                """.formatted(input, body);
    }

    /** The same, with a guard that establishes the invariant. */
    private static String guarded(String input, String body, String guard) {
        return TYPES + """

                behavior make : (%s) -> NonNeg | TooSmall
                    constructs NonNeg, TooSmall
                let make (x) = {
                    guard %s else TooSmall
                    %s
                }
                """.formatted(input, guard, body);
    }

    @ParameterizedTest(name = "{0}")
    @ValueSource(strings = {
            "NonNeg { id = x.id, n = x.n }",
            "NonNeg { ...x }",
    })
    void aRecordsFieldsAreOneConstructionHoweverTheyAreSupplied(String body) {
        reads(Verdict.UNKNOWN, unguarded("x: Common", body));
        reads(Verdict.PROVED, guarded("x: Common", body, "x.n >= 0"));
    }

    /**
     * A sum whose cases all spread one data is a spread source, and the field read off it is the
     * field every case carries — the same value the written-out spelling reads.
     */
    @ParameterizedTest(name = "{0}")
    @ValueSource(strings = {
            "NonNeg { id = x.id, n = x.n }",
            "NonNeg { ...x }",
    })
    void aSumsSharedPartIsOneConstructionHoweverItIsSupplied(String body) {
        reads(Verdict.UNKNOWN, unguarded("x: S", body));
        reads(Verdict.PROVED, guarded("x: S", body, "x.n >= 0"));
    }

    /** A spread naming a field path is bound before the construction, and reads the same place. */
    @ParameterizedTest(name = "{0}")
    @ValueSource(strings = {
            "NonNeg { id = x.inner.id, n = x.inner.n }",
            "NonNeg { ...x.inner }",
    })
    void aFieldPathIsOneConstructionHoweverItIsSupplied(String body) {
        reads(Verdict.UNKNOWN, unguarded("x: Box", body));
        reads(Verdict.PROVED, guarded("x: Box", body, "x.inner.n >= 0"));
    }

    private static final String MONEY = """
            module demo

            data Money = Decimal
                invariant nonNeg = value >= 0m

            data TooSmall
            """;

    /**
     * Closed arithmetic over a newtype builds one, and is that construction: what it is given is the
     * number its operands wrap, which is what writing the constructor around that subtraction gives
     * it. So the two are judged alike, and the guard that discharges one discharges the other.
     *
     * <p>What they do not share is {@code constructs}: re-wrapping a value of a type is not minting
     * one from raw data, and the authority to mint is written only where minting happens
     * (spec §newtype-arithmetic). That the two are one construction here and two things there is the
     * point — the invariant is owed wherever a value is built, and the authority is about where a
     * value comes from.
     */
    @ParameterizedTest(name = "{0}")
    @CsvSource(delimiter = '|', value = {
            "held - fee                     |",
            "Money(held.value - fee.value)  | constructs Money",
    })
    void arithmeticOverANewtypeIsTheConstructionItMakes(String body, String constructs) {
        reads(Verdict.UNKNOWN, MONEY + """

                behavior make : (held: Money, fee: Money) -> Money
                    %s
                let make (held, fee) = %s
                """.formatted(constructs == null ? "" : constructs, body));
        reads(Verdict.PROVED, MONEY + """

                behavior make : (held: Money, fee: Money) -> Money | TooSmall
                    constructs %s TooSmall
                let make (held, fee) = {
                    guard fee <= held else TooSmall
                    %s
                }
                """.formatted(constructs == null ? "" : "Money,", body));
    }

    /**
     * A value opened is judged as a value chosen is.
     *
     * <p>Two ways of writing one choice: a {@code match} over a sum, and an {@code if} over what
     * decides it. The check named the second and not the first, so a construction over what a
     * {@code match} answered was left to the run-time check while the same construction over an
     * {@code if} was reported — the same spelling difference this issue is about, at another node.
     */
    @ParameterizedTest(name = "{0}")
    @ValueSource(strings = {
            "match i.s with | A -> i.n | B -> 0 - i.n",
            "if i.flag then i.n else 0 - i.n",
    })
    void aChoiceIsJudgedHoweverItIsWritten(String chosen) {
        reads(Verdict.UNKNOWN, """
                module demo

                data A
                data B
                data S = A | B
                data In = { s: S, flag: Bool, n: Int }

                data NonNeg = Int
                    invariant nonNegative = value >= 0

                behavior make : (i: In) -> NonNeg
                    constructs NonNeg
                let make (i) = NonNeg(%s)
                """.formatted(chosen));
    }

    /** A construction the values themselves refute is refuted whichever way it is written. */
    @Test
    void aRefutedConstructionIsRefutedInEitherSpelling() {
        reads(Verdict.REFUTED_ALONE, MONEY + """

                behavior make : (held: Money) -> Money
                    constructs Money
                let make (held) = Money(0m - 1m)
                """);
    }

    /** The verdicts this check reached on constructions of {@code NonNeg} or {@code Money}, which is
     * where a construction that was never judged at all shows up: as none. */
    private static void reads(Verdict expected, String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } catch (souther.compiler.diag.CompileException refused) {
            // A construction the values refute is an error, and the verdict that says so was reached
            // before it was raised. So which verdict is what is asked, and not whether it compiles —
            // but only where a refutation is what was expected. Any other refusal is this test's own
            // program being wrong, and swallowing it would leave `no construction was judged`
            // standing for `the module did not compile`.
            if (!expected.refuted()) {
                throw refused;
            }
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> reached = said.stream().map(Said::verdict).toList();
        assertFalse(reached.isEmpty(), "no construction was judged at all");
        assertEquals(List.of(expected), reached);
    }
}
