package souther.compiler.partition;

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
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A remainder of a form is looked for twice: its numbers walked with the last held to the class the
 * others leave it, and after that the values of the form walked class by class. Where both come
 * back with nothing, what stopped the first is said beside what the second met; where the second
 * proves there is nothing, the proof is the answer.
 *
 * <p>The item is the remainder of a sum of numbers each held from nought to five, by a thousand,
 * above twenty-five. No value of the sum is above twenty-five, so neither walk finds a row. Over
 * five numbers the first walk tries more values together than it may and stops at that figure;
 * the second has no member of any class to try and stops at nothing, and is no proof, since the
 * item is a run and not a level. Over two numbers the first walk tries every value and stops at
 * nothing either.
 */
class WhatTheWalkOfARemaindersNumbersFellShortOfIsSaidBesideTheClassWalkTest {

    private static final CompositionBudget TOGETHER =
            CompositionBudget.VALUES_THE_POSITIONS_ON_THE_WAY_ARE_TRIED_AT;

    private static final BigInteger DIVISOR = BigInteger.valueOf(1000);

    @Test
    void whereTheClassWalkFindsNothingTooTheFigureTheNumbersStoppedAtIsSaid() {
        Realization.Unknown unknown = assertInstanceOf(Realization.Unknown.class,
                realized(5, above(25)));
        assertTrue(unknown.stoppedBy().contains(TOGETHER), unknown::toString);
    }

    @Test
    void aWalkOfFewNumbersThatTriedThemAllSaysNoSuchFigure() {
        Realization.Unknown unknown = assertInstanceOf(Realization.Unknown.class,
                realized(2, above(25)));
        assertFalse(unknown.stoppedBy().contains(TOGETHER), unknown::toString);
    }

    /** At a level the sum never comes to, the class walk proves it, whatever stopped the first. */
    @Test
    void whereTheClassWalkProvesThereIsNothingTheProofIsTheAnswer() {
        assertInstanceOf(Realization.Impossible.class, realized(5,
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(30))));
    }

    private static Realization realized(int numbers, Criterion where) {
        List<String> names = new ArrayList<>();
        for (int i = 0; i < numbers; i++) {
            names.add("n" + i);
        }
        SearchRegion region = quantities(names);
        Map<NumericTerm, ExactRatio> sum = new LinkedHashMap<>();
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        TermPath[] paths = new TermPath[numbers];
        for (int i = 0; i < numbers; i++) {
            NumericTerm term = new NumericTerm.ValueOf(TermPath.of(names.get(i)));
            paths[i] = TermPath.of(names.get(i));
            sum.put(term, ExactRatio.ONE);
            on.put(term, Carrier.WHOLE);
            region = region
                    .assuming(new LinearForm<>(ExactRatio.ZERO, Map.of(term, ExactRatio.ONE
                            .negated())), Rel.LE).taken()
                    .assuming(new LinearForm<>(ExactRatio.of(-5), Map.of(term, ExactRatio.ONE)),
                            Rel.LE).taken();
        }
        Standing remainder = new Standing.OfARemainder(new LinearForm<>(ExactRatio.ZERO, sum), on,
                LevelSpace.steppingBy(ExactRatio.ONE), DIVISOR,
                Standing.OfARemainderAndAForm.every(DIVISOR), where);
        return new LevelRealizer().realize(remainder, region,
                NothingTheDeclarationsRefuse.at(paths));
    }

    /** The values of the remainder above {@code line}. */
    private static Criterion above(long line) {
        LevelSpace space = LevelSpace.steppingBy(ExactRatio.ONE);
        Seam parted = HeldSeams.of(space, Level.OfTheQuantity.of(line), Towards.BELOW);
        return new Criterion.Within(
                new Band(Band.endAt(parted, null, Towards.ABOVE),
                        Band.endAt(null, null, Towards.BELOW)),
                null, Towards.ABOVE);
    }

    private static SearchRegion quantities(List<String> names) {
        StringBuilder parameters = new StringBuilder();
        for (String name : names) {
            parameters.append(parameters.isEmpty() ? "" : ", ").append(name).append(": Int");
        }
        Compilation compilation = ACompiledModel.answered("""
                module example.remainder

                data Ok = { v: Int }

                behavior f : (%s) -> Ok
                    constructs Ok

                let f (%s) = Ok { v = 1 }
                """.formatted(parameters, String.join(", ", names)));
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles and reads its input");
        return inputs.quantities(rules).region();
    }
}
