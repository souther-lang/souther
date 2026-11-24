package souther.compiler.partition;

import java.util.Map;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The values the rules name a position at are read before the item's walk, and a value whose level
 * this compiler could not hold is said beside what the walk comes back with.
 *
 * <p>The position is held to ten and twenty, and the item is the position weighed by ten to the
 * greatest power there is, above nought: what ten comes to has no representation, so the values
 * named settle nothing, and the walk of the form that is asked after them finds no row either.
 * Weighed by one, every value named is read and nothing is said of a number not held.
 */
class AValueNamedThatComesToANumberNotHeldIsSaidBesideTheWalkTest {

    private static final CompositionCapacity NOT_HELD = new CompositionCapacity(
            CompositionCapacity.Where.WHAT_A_VALUE_NAMED_COMES_TO,
            UnheldNumber.NO_REPRESENTATION_EXISTS);

    private static final TermPath C = TermPath.of("c");

    private static final NumericTerm TERM = new NumericTerm.ValueOf(C);

    @Test
    void whereTheWalkSettlesNothingTheNumberNotHeldIsSaid() {
        Realization.Unknown unknown = assertInstanceOf(Realization.Unknown.class,
                realized(ExactRatio.tenTo(Long.MAX_VALUE), aboveNought()));
        assertTrue(unknown.unheld().contains(NOT_HELD), unknown::toString);
    }

    @Test
    void whereEveryValueIsReadNoSuchNumberIsSaid() {
        Realization made = realized(ExactRatio.ONE, aboveNought());
        assertFalse(made instanceof Realization.Unknown unknown
                && unknown.unheld().contains(NOT_HELD), made::toString);
    }

    /** At a level, the walk's proof is the answer whatever the values named came to. */
    @Test
    void whereTheWalkProvesThereIsNothingTheProofIsTheAnswer() {
        assertInstanceOf(Realization.Impossible.class, realized(ExactRatio.tenTo(Long.MAX_VALUE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(1))));
    }

    /** A form's constant belongs to its levels, which the walk puts the coefficients at. */
    @Test
    void aFormWithAConstantIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> new Standing.OfAForm(
                new LinearForm<>(ExactRatio.ONE, Map.of(TERM, ExactRatio.ONE)),
                Map.of(TERM, Carrier.WHOLE), LevelSpace.steppingBy(ExactRatio.ONE),
                aboveNought()));
    }

    private static Realization realized(ExactRatio weight, Criterion where) {
        Standing standing = new Standing.OfAForm(
                new LinearForm<>(ExactRatio.ZERO, Map.of(TERM, weight)),
                Map.of(TERM, Carrier.WHOLE), LevelSpace.steppingBy(ExactRatio.ONE), where);
        return new LevelRealizer().realize(standing, region(),
                NothingTheDeclarationsRefuse.at(C));
    }

    private static Criterion aboveNought() {
        Seam parted = HeldSeams.of(LevelSpace.steppingBy(ExactRatio.ONE),
                Level.OfTheQuantity.of(0), Towards.BELOW);
        return new Criterion.Within(new Band(Band.endAt(parted, null, Towards.ABOVE),
                Band.endAt(null, null, Towards.BELOW)), null, Towards.ABOVE);
    }

    private static SearchRegion region() {
        Compilation compilation = ACompiledModel.answered("""
                module example.named

                data Code = Int
                    invariant value == 10 || value == 20

                data Ok = { v: Int }

                behavior f : (c: Code) -> Ok
                    constructs Ok

                let f (c) = Ok { v = 1 }
                """);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        return inputs.quantities(rules).region();
    }
}
