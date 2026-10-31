package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A walk asked for numbers meeting a congruence offers only assignments that meet it, whatever
 * order the numbers stand on.
 *
 * <p>What the walk hands back as found is a witness of every constraint it was handed, and a
 * congruence is one of them: an assignment outside the class is no witness of it, and a row
 * built from one stands somewhere else. Held at every assignment the walk offers to be composed,
 * and not only at the first — a walk stepped past what it offered first, as a search that built a
 * row there and wants another does, offers the next — and on two orders: whole numbers, and days,
 * where a remainder of the days between two dates is what a weekday is.
 *
 * <p>The oracle is the congruence worked out here at each offered assignment, over every residue
 * and every shift of the form by a constant, for a divisor of seven.
 */
class AWitnessOfACongruenceMeetsItOnEveryOrderTest {

    @Test
    void everyAssignmentOfferedOverDaysMeetsTheCongruence() {
        everyOfferedMeets("(s: Date, d: Date)");
    }

    @Test
    void everyAssignmentOfferedOverWholeNumbersMeetsTheCongruence() {
        everyOfferedMeets("(s: Int, d: Int)");
    }

    private static void everyOfferedMeets(String parameters) {
        Quantities quantities = quantities(parameters);
        NumericTerm.FromOnePosition s = new NumericTerm.ValueOf(TermPath.of("s"));
        NumericTerm.FromOnePosition d = new NumericTerm.ValueOf(TermPath.of("d"));
        BigInteger seven = BigInteger.valueOf(7);
        for (long shift = 0; shift < 7; shift++) {
            for (long residue = 0; residue < 7; residue++) {
                Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
                coefs.put(s, ExactRatio.of(-1));
                coefs.put(d, ExactRatio.ONE);
                NumericWitness.Congruent congruent = new NumericWitness.Congruent(
                        new LinearForm<>(ExactRatio.of(shift), coefs), seven,
                        BigInteger.valueOf(residue));
                List<Map<NumericTerm, Place>> offered = new ArrayList<>();
                // Each of the first three it offers is refused, as a search stepping past a row
                // it already built refuses it, so the walk has to offer more.
                NumericWitness.Composing refusingThree = standing -> {
                    offered.add(new LinkedHashMap<>(standing));
                    return offered.size() <= 3 ? new NumericWitness.Composed.NotBuilt(
                            CompositionShortfall.NONE) : new NumericWitness.Composed.Built();
                };
                NumericWitness.of(quantities.region(), List.of(s, d),
                        each -> quantities.ordersOf(each).answered(),
                        NothingTheDeclarationsNarrow.LOOKING, refusingThree, List.of(congruent));
                String said = "d - s + " + shift + " ≡ " + residue + " (mod 7) over " + parameters;
                assertFalse(offered.isEmpty(), said + ": some assignment is offered");
                for (Map<NumericTerm, Place> each : offered) {
                    long left = Math.floorMod(number(each.get(d)) - number(each.get(s)) + shift, 7);
                    assertEquals(residue, left, said + ": offered " + each);
                }
            }
        }
    }

    /** The whole number a place of either order counts to. */
    private static long number(Place place) {
        assertNotNull(place, "every number of the congruence stands somewhere");
        if (!(Count.number(place).exactly().floor() instanceof ExactAnswer.Held<BigInteger>(
                BigInteger whole))) {
            throw new AssertionError("a place counting to a whole number: " + place);
        }
        return whole.longValueExact();
    }

    private static Quantities quantities(String parameters) {
        Compilation compilation = Compilation.ofSource("""
                module example.congruent

                data Ok = { v: Int }

                behavior f : %s -> Ok
                    constructs Ok

                let f (s, d) = Ok { v = 1 }
                """.formatted(parameters), "Main");
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the model under test compiles and reads its input");
        return inputs.quantities(rules);
    }
}
