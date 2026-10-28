package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * A comparison asked twice of one reading comes back as an equal read each time, and each ask is
 * told the copy of the model's code it was read off by that ask alone.
 *
 * <p>What a comparison asks of a row is kept with the reading, so that the statements of a search
 * that name it are not each worked out again. A read handed out twice would be one read standing
 * in two asks, and the ask that came second would be told what the first said.
 */
class TwoAsksOfOneComparisonAreEachHandedAReadOfItsOwnTest {

    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int) -> Ok
            """;

    private static ModelOccurrence copy(int ordinal) {
        return new ModelOccurrence(SourceConstructOrigin.written(new WrittenOwner.Body("m", "f"),
                ordinal, SourceConstruct.BINARY), ExpansionLineage.ORIGINAL);
    }

    @Test
    void eachAskIsHandedAnEqualReadThatIsNotTheSameAndToldItsOwnCopy() {
        InputReading reading = reading();
        Proposition.Compared aboveNought = new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.ZERO, Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(pathOf(reading, "x"))), ExactRatio.ONE)), Rel.GT),
                true);
        ModelOccurrences first = ModelOccurrences.of(copy(1));
        ModelOccurrences second = ModelOccurrences.of(copy(2));

        DemandReading.Projected one =
                DemandReading.projectedOff(null, aboveNought, reading, first);
        DemandReading.Projected another =
                DemandReading.projectedOff(null, aboveNought, reading, second);

        assertEquals(1, one.reads().size());
        assertEquals(one.reads(), another.reads());
        assertNotSame(one.reads().getFirst(), another.reads().getFirst());
        assertEquals(first, one.readOff().of(one.reads().getFirst()));
        assertEquals(second, another.readOff().of(another.reads().getFirst()));
        assertEquals(second, another.readOff().of(another.reads().getFirst()),
                "and the second ask is not told what the first said");
    }

    private static TermPath pathOf(InputReading reading, String spelled) {
        return reading.domain().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError("no position at " + spelled));
    }

    private static InputReading reading() {
        Compilation compilation = Compilation.ofSources(List.of(PAIR), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext context =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("read"), context,
                TypeCardinality.Counts.workedOutIn(context), Membership.none()).reading(rules);
    }
}
