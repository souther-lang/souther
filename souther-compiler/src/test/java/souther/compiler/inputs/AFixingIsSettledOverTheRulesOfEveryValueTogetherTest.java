package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position fixed is settled over the rules of every value said together, wherever the value whose
 * rules name it stands.
 *
 * <p>What the declarations leave under a context is worked out once and shared by every reading a
 * search makes from it, and a fixing is said onto that afterwards in this input's names. So the
 * fixing reaches the rules of a value opened at a case, of a value opened inside a sequence, and of
 * two values that both name the number — each held below by what the fixed number does to a number
 * the rules relate it to, and by a pair the rules refuse being proved to leave nothing.
 *
 * <p>And what is taken in beside a fixing is spaced by what the number is and not by whether a rule
 * happened to name it. A number no clause mentions is spaced all the same, so a form over it is
 * taken in rather than refused.
 */
class AFixingIsSettledOverTheRulesOfEveryValueTogetherTest {

    /** A case whose own rules relate two of its fields. */
    private static final String UNDER_A_CASE = """
            module g

            data A = { lo: Int, hi: Int }
                invariant ordered = lo <= hi
            data B = { y: Int }
            data Q = A | B

            data Holder = { q: Q }

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    @Test
    void aFixingUnderACaseReachesTheRulesOfThatCase() {
        InputDomain read = reading(UNDER_A_CASE);
        Quantities asked = read.quantities(rulesOf(UNDER_A_CASE));
        NumericTerm lo = valueAt(read, "h.q@A.lo");
        NumericTerm hi = valueAt(read, "h.q@A.hi");

        assertEquals(Endpoint.inclusive(count(3)),
                asked.given(lo, count(3)).runsBetween(hi).min(),
                "the case's rule holds hi at or above where lo was fixed");
    }

    @Test
    void aPairTheCaseRefusesLeavesNothing() {
        InputDomain read = reading(UNDER_A_CASE);
        Quantities asked = read.quantities(rulesOf(UNDER_A_CASE));

        assertTrue(asked.given(valueAt(read, "h.q@A.lo"), count(5))
                        .given(valueAt(read, "h.q@A.hi"), count(2)).emptiness().isPresent(),
                "lo at five and hi at two is a pair the case's rule refuses");
    }

    /** A value inside a sequence whose own rules relate two of its fields. */
    private static final String INSIDE_A_SEQUENCE = """
            module g

            data Item = { lo: Int, hi: Int }
                invariant ordered = lo <= hi

            data Cart = { items: List<Item> }

            data Ok

            behavior read : (c: Cart) -> Ok
            """;

    private static final NumericTerm ITEM_LO = new NumericTerm.ValueOf(
            TermPath.of("c").then("items").element().then("lo"));
    private static final NumericTerm ITEM_HI = new NumericTerm.ValueOf(
            TermPath.of("c").then("items").element().then("hi"));

    @Test
    void aFixingInsideASequenceReachesTheRulesOfWhatItHolds() {
        Quantities asked = reading(INSIDE_A_SEQUENCE).quantities(rulesOf(INSIDE_A_SEQUENCE));

        assertEquals(Endpoint.inclusive(count(3)),
                asked.given(ITEM_LO, count(3)).runsBetween(ITEM_HI).min(),
                "the element's rule holds hi at or above where lo was fixed");
    }

    @Test
    void aPairTheElementRefusesLeavesNothing() {
        Quantities asked = reading(INSIDE_A_SEQUENCE).quantities(rulesOf(INSIDE_A_SEQUENCE));

        assertTrue(asked.given(ITEM_LO, count(5)).given(ITEM_HI, count(2))
                        .emptiness().isPresent(),
                "lo at five and hi at two is a pair the element's rule refuses");
    }

    /**
     * One number the rules of two values name: the case's own, and the record the sum sits in
     * through a field every case spreads.
     */
    private static final String NAMED_BY_TWO = """
            module g

            data Shared = { lo: Int, hi: Int }
            data A = { ...Shared, x: Int }
                invariant above = lo <= x
            data B = { ...Shared, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant ordered = q.lo <= q.hi

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    @Test
    void aNumberTwoValuesNameIsSettledForTheRulesOfBoth() {
        InputDomain read = reading(NAMED_BY_TWO);
        Quantities fixed = read.quantities(rulesOf(NAMED_BY_TWO))
                .given(valueAt(read, "h.q@A.lo"), count(3));

        assertEquals(Endpoint.inclusive(count(3)),
                fixed.runsBetween(valueAt(read, "h.q@A.hi")).min(),
                "the record's rule about the shared names holds hi at or above lo");
        assertEquals(Endpoint.inclusive(count(3)),
                fixed.runsBetween(valueAt(read, "h.q@A.x")).min(),
                "the case's own rule holds x at or above lo");
    }

    @Test
    void aPairEitherValueRefusesLeavesNothing() {
        InputDomain read = reading(NAMED_BY_TWO);
        Quantities asked = read.quantities(rulesOf(NAMED_BY_TWO));
        NumericTerm lo = valueAt(read, "h.q@A.lo");

        assertTrue(asked.given(lo, count(5)).given(valueAt(read, "h.q@A.hi"), count(2))
                        .emptiness().isPresent(),
                "refused by the record's rule");
        assertTrue(asked.given(lo, count(5)).given(valueAt(read, "h.q@A.x"), count(2))
                        .emptiness().isPresent(),
                "refused by the case's rule");
    }

    /** Two numbers no clause mentions. */
    private static final String UNRULED = """
            module g

            data P = { x: Int, y: Int }

            data Ok

            behavior read : (p: P) -> Ok
            """;

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("p").then("x"));
    private static final NumericTerm Y = new NumericTerm.ValueOf(TermPath.of("p").then("y"));

    /**
     * A form over a fixed number no clause mentions is taken in, and solved with the fixing.
     *
     * <p>Whether a form can be taken in is whether every number in it is spaced. Nothing the
     * declarations say mentions {@code x}, and fixing it settles nothing in the rules of {@code P}
     * before they are said together — so what spaces it is its type, and not a rule that happened to
     * be about it.
     */
    @Test
    void aFormOverAFixedNumberNoRuleMentionsIsTakenIn() {
        SearchRegion fixed = reading(UNRULED).quantities(rulesOf(UNRULED)).region()
                .given(X, count(3));

        SearchRegion.Assumption taken = fixed.assuming(sum(), Rel.LE);

        assertInstanceOf(SearchRegion.Assumption.Taken.class, taken,
                "x and y are both spaced, though no rule names either");
        assertEquals(Endpoint.inclusive(count(2)),
                runsBetween(((SearchRegion.Assumption.Taken) taken).region(),
                        LinearForm.atom(Y)).max(),
                "x at three and x + y at most five leave y at most two");
    }

    /** And the same with the form taken in before the number is fixed. */
    @Test
    void theSameWhicheverArrivesFirst() {
        SearchRegion region = reading(UNRULED).quantities(rulesOf(UNRULED)).region();

        SearchRegion.Assumption taken = region.assuming(sum(), Rel.LE);

        assertInstanceOf(SearchRegion.Assumption.Taken.class, taken);
        assertEquals(Endpoint.inclusive(count(2)),
                runsBetween(((SearchRegion.Assumption.Taken) taken).region().given(X, count(3)),
                        LinearForm.atom(Y)).max());
    }

    /**
     * Fixing works out nothing the declarations leave under a context again.
     *
     * <p>Counted rather than timed. A search tries a candidate per value at every position it fixes,
     * and what is held is that each of them is said onto one answer about the context rather than
     * being a context of its own.
     */
    @Test
    void fixingWorksOutNothingAContextLeavesAgain() {
        InputDomain read = reading(NAMED_BY_TWO);
        Quantities asked = read.quantities(rulesOf(NAMED_BY_TWO));
        NumericTerm lo = valueAt(read, "h.q@A.lo");
        NumericTerm hi = valueAt(read, "h.q@A.hi");
        long beforeAsking = ReadQuantities.contextsRead();
        asked.runsBetween(hi);
        asked.given(lo, count(0)).emptiness();
        long before = ReadQuantities.contextsRead();
        // The count is kept where the work is done, so fixing that works nothing out is a count
        // that stood still and not a count nobody kept.
        assertTrue(before > beforeAsking, "asking about a context worked nothing out");

        for (int at = 0; at <= 5; at++) {
            Quantities fixed = asked.given(lo, count(at));
            fixed.runsBetween(hi);
            fixed.emptiness();
        }

        assertEquals(before, ReadQuantities.contextsRead());
    }

    private static LinearForm<NumericTerm> sum() {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(X, ExactRatio.ONE);
        coefs.put(Y, ExactRatio.ONE);
        return new LinearForm<>(ExactRatio.of(-5), coefs);
    }

    /** Where the form runs, of a region that holds something. */
    private static NumericDomain.Bounds runsBetween(SearchRegion within,
                                                    LinearForm<NumericTerm> form) {
        return switch (within.projectionOf(form)) {
            case NumericDomain.FormProjection.Within(NumericDomain.Bounds runs) -> runs;
            case NumericDomain.FormProjection.NothingIsLeft _ ->
                    throw new AssertionError("these rules leave a value: " + form);
            case null -> null;
        };
    }

    private static Count count(int at) {
        return new Count(BigDecimal.valueOf(at));
    }

    private static NumericTerm valueAt(InputDomain read, String spelled) {
        return new NumericTerm.ValueOf(read.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + read.positions().stream()
                                .map(Position::path).toList())));
    }

    private static RuleReadingSource rulesOf(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static InputDomain reading(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        return InputDomain.of(sigs.get("read"),
                RuleReadingContext.unshared(RuleReadings.of(compilation, module),
                        ReadAs.THE_COMPILATION_DOES),
                souther.compiler.carrier.Membership.none());
    }
}
