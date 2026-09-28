package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A contradiction taken into a real region reaches a real search as the model's word.
 *
 * <p><b>The wiring, held end to end once.</b> What the rules leave is worked out in one place and
 * what a search does about it is decided in another; between them the answer crosses a reading, a
 * region and a face of it, and every one of those hops is somewhere the answer that is not a range
 * can be read back as one. The pieces are held apart elsewhere against regions written by hand,
 * which answer whatever a check needs and cannot say whether the pieces are joined.
 *
 * <p>Two conditions closing the region between them, which is what an author writes one guard at a
 * time. Neither of them is unusual and no position is fixed: what contradicts is the pair, over both
 * positions at once.
 */
class AContradictionTakenIntoARegionReachesTheSearchAsAProofTest {

    /** Two positions with no rule of their own, so everything narrowing them is taken in here. */
    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int) -> Ok
            """;

    /**
     * The region answers with the proof rather than with a range.
     *
     * <p>The hop the rest of this rests on. Both readings of these rules write down no end at either
     * side, and one of them means every value there is.
     */
    @Test
    void theRegionAnswersWithTheProofAndNotWithARange() {
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                contradicting().projectionOf(term("x")),
                "the two conditions leave no assignment, so the position is at no value");
        assertInstanceOf(NumericDomain.FormProjection.NothingIsLeft.class,
                contradicting().projectionOf(sum()),
                "and neither is what the two positions add up to");
    }

    /** And with only the first of them taken in it is a range like any other. */
    @Test
    void andWithOnlyOneOfThemItIsARangeLikeAnyOther() {
        assertInstanceOf(NumericDomain.FormProjection.Within.class,
                region().assuming(form(-1, 1, 0), Rel.LE).taken().projectionOf(term("x")),
                "one condition on its own leaves every pair it admits");
    }

    /**
     * A search handed that region comes back with the proof, having walked nothing.
     *
     * <p>Which is the sentence this is all about, asked of the pieces as they are actually joined: a
     * region some conditions narrowed, a search that asks it where a position runs, and an answer a
     * reader may act on.
     */
    @Test
    void aSearchHandedThatRegionComesBackWithTheProof() {
        assertInstanceOf(NumericWitness.Standing.ProvedImpossible.class,
                NumericWitness.of(contradicting(), List.of(term("x")), _ -> Carrier.WHOLE,
                        NothingTheDeclarationsNarrow.LOOKING),
                "the rules were shown to leave nothing, so nothing was walked in it");
    }

    /** And the same search, over the region before the second condition, walks it. */
    @Test
    void andOverTheRegionBeforeThatConditionItWalks() {
        assertInstanceOf(NumericWitness.Standing.Found.class,
                NumericWitness.of(region().assuming(form(-1, 1, 0), Rel.LE).taken(),
                        List.of(term("x")), _ -> Carrier.WHOLE,
                        NothingTheDeclarationsNarrow.LOOKING),
                "there is somewhere for the position to stand, so it stands there");
    }

    /** The region with {@code y <= x} and {@code y >= x + 1} taken in, which no pair satisfies. */
    private static SearchRegion contradicting() {
        return region().assuming(form(-1, 1, 0), Rel.LE).taken()
                .assuming(form(1, -1, 1), Rel.LE).taken();
    }

    /** {@code cx·x + cy·y + k} over the two positions the behavior declares. */
    private static LinearForm<NumericTerm> form(long cx, long cy, long k) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(term("x"), ExactRatio.of(cx));
        coefs.put(term("y"), ExactRatio.of(cy));
        return new LinearForm<>(ExactRatio.of(k), coefs);
    }

    private static LinearForm<NumericTerm> sum() {
        return form(1, 1, 0);
    }

    private static final Read READ = read();

    private static SearchRegion region() {
        return READ.input().quantities(READ.rules()).region();
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(pathOf(spelled));
    }

    private static TermPath pathOf(String spelled) {
        return READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + READ.input().positions().stream()
                                .map(Position::path).toList()));
    }

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static Read read() {
        Compilation compilation =
                Compilation.ofSources(List.of(PAIR), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return new Read(InputDomain.of(sigs.get("read"),
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES)), rules);
    }
}
