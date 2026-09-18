package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a row writes a value is a place on the position's order, whatever kind of place that is.
 *
 * <p>A count is one kind and a string is the other. Fixing took a count, so every value a carrier
 * that counts nothing offered had to be dropped by whoever was choosing one — and a position whose
 * values were in hand came back as a position nothing could compose a value for. What the caller
 * then read was a condition on the way reported as unrepresented, at a position the rules had
 * narrowed to a single value.
 *
 * <p>Held at the two places that decide it. A region answers where a fixed position runs and says
 * when two fixings leave nothing; the walk that chooses a value reads that answer and puts one
 * back. A test of either alone passes while the other drops the value on the floor.
 *
 * <p>Both kinds of place in each, since what is being held is that the vocabulary is the place and
 * not that strings are a case. Checked on a count alone, the answer would be the same one this
 * already gave.
 */
class APositionStandsAtAPlaceAndNotAtANumberTest {

    private static final String MODEL = """
            module example.places

            data Ok = { v: Int }

            behavior f : (s: String, n: Int) -> Ok
                constructs Ok

            let f (s, n) = Ok { v = 1 }
            """;

    /** A position fixed at a place of its order runs between that place and itself. */
    @Test
    void aPositionFixedAtAPlaceRunsBetweenThatPlaceAndItself() {
        assertEquals("[spring, spring]", runsAfterFixing("s", Text.of("spring")));
        assertEquals("[7, 7]", runsAfterFixing("n", new Count(BigDecimal.valueOf(7))));
    }

    /**
     * And a position fixed twice at two places is fixed at nothing, whichever kind they are.
     *
     * <p>The proof names both places. Read off a fixing that had dropped one of them, a position
     * fixed at two strings would have come back holding whichever the reader still had.
     */
    @Test
    void aPositionFixedAtTwoPlacesIsFixedAtNothing() {
        EmptyInput.TwoValuesAtOnePosition text = twoValues("s",
                Text.of("autumn"), Text.of("spring"));
        assertEquals(List.of("autumn", "spring"),
                List.of(text.one().key(), text.other().key()));
        EmptyInput.TwoValuesAtOnePosition counted = twoValues("n",
                new Count(BigDecimal.ONE), new Count(BigDecimal.TWO));
        assertEquals(List.of("1", "2"),
                List.of(counted.one().key(), counted.other().key()));
    }

    /**
     * And the walk that chooses a value for a position puts one back on either order.
     *
     * <p>The other end of the same contract. The region can hold a string and the walk is what asks
     * it for one, so a walk that went on dropping what it was offered would leave the condition on
     * the way reported as one nothing composed a value at — which is the sentence this was found
     * through.
     */
    @Test
    void theWalkComposesAValueOnEitherOrder() {
        assertNotNull(composedFor("s"), "a string position is one a value can be chosen for");
        assertNotNull(composedFor("n"), "and so is a counted one");
        assertInstanceOf(Text.class, composedFor("s"),
                "the value composed for a string position is a place of its own order");
    }

    /** Where {@code path} runs once it has been fixed at {@code at}, as the two ends. */
    private static String runsAfterFixing(String path, Place at) {
        NumericTerm.FromOnePosition term = new NumericTerm.ValueOf(TermPath.of(path));
        NumericDomain.Bounds runs = assertInstanceOf(
                NumericDomain.FormProjection.Within.class,
                region().given(term, at).projectionOf(term),
                "a fixed position runs somewhere").bounds();
        assertNotNull(runs, "a fixed position runs somewhere");
        return "[" + runs.min().at().key() + ", " + runs.max().at().key() + "]";
    }

    /** The proof that fixing {@code path} at both places leaves nothing. */
    private static EmptyInput.TwoValuesAtOnePosition twoValues(String path, Place one, Place other) {
        NumericTerm.FromOnePosition term = new NumericTerm.ValueOf(TermPath.of(path));
        Optional<EmptyInput> empty = region().given(term, one).given(term, other).emptiness();
        assertTrue(empty.isPresent(), () -> path + " was fixed at two places and holds neither");
        return assertInstanceOf(EmptyInput.TwoValuesAtOnePosition.class, empty.get());
    }

    /** The place the walk chose for {@code path}, or null where it chose none. */
    private static Place composedFor(String path) {
        NumericTerm.FromOnePosition term = new NumericTerm.ValueOf(TermPath.of(path));
        Quantities quantities = quantities();
        NumericWitness.Standing stood = NumericWitness.of(quantities.region(), List.of(term),
                each -> quantities.ordersOf(each).answered(),
                NothingTheDeclarationsNarrow.LOOKING);
        return stood instanceof NumericWitness.Standing.Found found ? found.at().get(term) : null;
    }

    private static SearchRegion region() {
        return quantities().region();
    }

    private static Quantities quantities() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs =
                compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles and reads its input");
        return inputs.quantities(rules);
    }
}
