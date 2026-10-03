package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.lang.reflect.Field;
import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a region holds anything is worked out once for that region.
 *
 * <p>A search asks the region it is about to realise a level in, and asks it again while choosing a
 * value there. The answer is a function of the region — of what is fixed in it and what was taken
 * in — and a region does not change once it is made, so the second asking is the first one's answer.
 * What does change it is a refinement, and a refinement is another region that has worked out
 * nothing.
 *
 * <p>What is read is what the region keeps, by reflection, because that a region kept its answer is
 * not anything a caller is offered to ask. A time would be a fact about the machine it was taken on.
 */
class ARegionWorksOutWhetherItIsEmptyOnceTest {

    /** Two positions, one to a parameter, related by nothing until a test takes {@code y <= 2x} in. */
    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int) -> Ok
            """;

    /** A proof asked for twice is the one proof, and not the same proof made again. */
    @Test
    void aProofIsTheAnswerItWasTheFirstTime() {
        SearchRegion refused = related()
                .given(term("y"), Count.of(BigDecimal.valueOf(100)))
                .given(term("x"), Count.of(BigDecimal.ZERO));

        Optional<EmptyInput> first = refused.emptiness();
        assertTrue(first.isPresent(), "y at 100 and x at 0 is refused by y <= 2x");
        assertSame(first, refused.emptiness(),
                "the region was asked the same question about the same values");
    }

    /**
     * And that nothing was proved is an answer, kept the same way.
     *
     * <p>Kept only where something was proved, a region that holds a value — which is every region
     * a search goes on to choose in — would walk its cases again every time it was asked.
     */
    @Test
    void thatNothingWasProvedIsKeptAsWellAsAProof() {
        SearchRegion admitted = related()
                .given(term("y"), Count.of(BigDecimal.valueOf(100)))
                .given(term("x"), Count.of(BigDecimal.valueOf(50)));

        assertNull(kept(admitted), "nothing has asked yet, so nothing has been worked out");
        assertEquals(Optional.empty(), admitted.emptiness(),
                "y at 100 and x at 50 is on the line y <= 2x draws");
        assertEquals(Optional.empty(), kept(admitted),
                "and what came back is what the region holds from now on");
    }

    /**
     * A refinement is asked afresh, whatever the region it came from had worked out.
     *
     * <p>The region before {@code x} is fixed holds a value and the one after does not, so an
     * answer carried across would say the second holds something it was shown not to.
     */
    @Test
    void aRefinementWorksItOutForItself() {
        SearchRegion before = related().given(term("y"), Count.of(BigDecimal.valueOf(100)));
        assertEquals(Optional.empty(), before.emptiness());

        SearchRegion after = before.given(term("x"), Count.of(BigDecimal.ZERO));
        assertNull(kept(after), "a refinement is made with nothing worked out");
        assertTrue(after.emptiness().isPresent(), "and what it works out is its own");
    }

    /**
     * A fixing already made is the region it was made in.
     *
     * <p>The same values fixed at the same places, which is the same question, and a copy of the
     * region would work out again everything the region had already answered.
     */
    @Test
    void aFixingAlreadyMadeLeavesTheRegionAsItWas() {
        SearchRegion fixed = related().given(term("y"), Count.of(BigDecimal.valueOf(100)));

        assertSame(fixed, fixed.given(term("y"), Count.of(BigDecimal.valueOf(100))));
    }

    /** And a different value at the same place is a different region, which two values are. */
    @Test
    void aSecondValueAtTheSamePlaceIsARefinement() {
        SearchRegion fixed = related().given(term("y"), Count.of(BigDecimal.valueOf(100)));
        SearchRegion twice = fixed.given(term("y"), Count.of(BigDecimal.valueOf(101)));

        assertNotSame(fixed, twice);
        assertTrue(twice.emptiness().orElseThrow() instanceof EmptyInput.TwoValuesAtOnePosition,
                "y at 100 and at 101 is no value of y");
    }

    /** What the region has worked out about whether it holds anything, or null where nothing has. */
    private static Optional<?> kept(SearchRegion region) {
        try {
            Field held = ReadQuantities.class.getDeclaredField("emptiness");
            held.setAccessible(true);
            return (Optional<?>) held.get(((ReadRegion) region).within());
        } catch (ReflectiveOperationException e) {
            throw new LinkageError(e.getMessage(), e);
        }
    }

    /** The region with {@code y - 2x <= 0} taken in. */
    private static SearchRegion related() {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(term("y"), ExactRatio.ONE);
        coefs.put(term("x"), ExactRatio.of(-2));
        return region().assuming(new LinearForm<>(ExactRatio.ZERO, coefs), Rel.LE).taken();
    }

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static final Read READ = read();

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError("no position at " + spelled)));
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(PAIR), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return new Read(InputDomain.of(sigs.get("read"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)), rules);
    }
}
