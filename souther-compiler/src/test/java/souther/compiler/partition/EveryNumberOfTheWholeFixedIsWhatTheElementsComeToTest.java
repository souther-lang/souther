package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link ContainerAsAWhole.Fixed} hands over comes to every number of the whole it fixed, and
 * a group of elements is read with those numbers where they are fixed.
 *
 * <p>Two totals of one place — what the numbers come to, and what each plus one comes to — are
 * one number of the place for so many elements, and the two agree or no elements meet both. The
 * oracle is the arithmetic: each total worked out of the values handed back, and the two agreeing
 * exactly where the second is the first and one for each element.
 */
class EveryNumberOfTheWholeFixedIsWhatTheElementsComeToTest {

    private static final String SOURCE = """
            module g

            data Ok

            behavior counted : (xs: List<Int>) -> Ok
            """;

    private record Read(Quantities measuring, RuleReadingContext reading, TermPath xs,
                        TypeView view, NumericTerm total, NumericTerm totalOfEachAndOne) {}

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(SOURCE), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals("xs")).findFirst().orElseThrow();
        ValueName.Stdlib sum = ValueName.Stdlib.operation("List", "sum");
        NumericTerm total = NumericTerm.TakenOver.of(sum,
                new RunSource.ProjectedOccurrences(xs.element()), Type.INT, rules.inners(),
                rules.symbols());
        ElementValue eachAndOne = new ElementValue.Affine(new LinearForm<>(ExactRatio.ONE,
                Map.of(ElementProjection.ofFields(List.of()), ExactRatio.ONE)));
        NumericTerm totalOfEachAndOne = NumericTerm.TakenOver.of(sum,
                new RunSource.ComputedOccurrences(xs.element(), eachAndOne, Type.INT, null),
                Type.INT, rules.inners(), rules.symbols());
        TypeView view = TypeView.of(new Type.ListOf(Type.INT), rules.inners(), rules.symbols(),
                rules.kinds(), rules.sums());
        return new Read(input.quantities(rules), reading, xs, view, total, totalOfEachAndOne);
    }

    private static ContainerAsAWhole.ATotal asked(Read read, NumericTerm term, long at) {
        return new ContainerAsAWhole.ATotal(term, new NumericSet.At(Count.of(at)), Count.of(at),
                read.measuring().ordersOf(term));
    }

    private static ContainerAsAWhole whole(Read read, List<ContainerAsAWhole.ATotal> totals,
                                           long many) {
        ContainerAsAWhole whole = ContainerAsAWhole.of(read.xs(), read.view(), List.of(), totals,
                Map.of(), new NumericSet.At(Count.of(many)), read.measuring(),
                read.measuring().region(), read.reading());
        assertNotNull(whole, "whole numbers are fixed");
        return whole;
    }

    private static long totalOf(List<ObservedValue> values, long eachAdds) {
        long out = 0;
        for (ObservedValue each : values) {
            out += ((ObservedValue.Integer) each).value() + eachAdds;
        }
        return out;
    }

    /**
     * Every choice of the two totals for two elements: the elements handed back come to both,
     * and where the second is not the first and two, none are handed back and the choice is said
     * to ask two things of the place.
     */
    @Test
    void twoTotalsOfOnePlaceAreMetTogetherOrNotAtAll() {
        Read read = read();
        List<ObservedValue> drawn = List.of(new ObservedValue.Integer(0),
                new ObservedValue.Integer(0));
        int met = 0;
        int refused = 0;
        List<List<Place>> every = new ArrayList<>();
        List<ContainerAsAWhole> wholes = new ArrayList<>();
        for (long second : List.of(6L, 7L, 8L)) {
            ContainerAsAWhole whole = whole(read, List.of(asked(read, read.total(), 5),
                    asked(read, read.totalOfEachAndOne(), second)), 2);
            for (List<Place> chosen : whole.choices().each()) {
                every.add(chosen);
                wholes.add(whole);
            }
        }
        assertEquals(3, every.size(), "one choice of each pair");
        for (int each = 0; each < every.size(); each++) {
            List<Place> chosen = every.get(each);
            ContainerAsAWhole whole = wholes.get(each);
            ContainerAsAWhole.Fixed fixed = whole.at(chosen);
            Map<NumericTerm, Place> at = fixed.beside(Map.of());
            long first = Count.number(at.get(read.total())).at().longValueExact();
            long second = Count.number(at.get(read.totalOfEachAndOne())).at().longValueExact();
            boolean agree = second == first + 2;
            assertEquals(agree, fixed.comesTogetherIn(2), chosen::toString);
            List<ObservedValue> values = fixed.spread(drawn, null, 0, _ -> List.of(),
                    _ -> NumericDomain.Bounds.OPEN);
            if (agree) {
                assertNotNull(values, chosen::toString);
                assertEquals(first, totalOf(values, 0), "the first total, read back");
                assertEquals(second, totalOf(values, 1), "the second total, read back");
                met++;
            } else {
                assertNull(values, chosen::toString);
                refused++;
            }
        }
        assertEquals(1, met, "five and seven agree");
        assertEquals(2, refused, "five and six, five and eight do not");
    }

    /** Where the region leaves the place nothing, there is no run to move an element inside, and
     *  no elements are handed back: nothing left is not every number. */
    @Test
    void aPlaceTheRegionLeavesNothingMovesNoElement() {
        Read read = read();
        ContainerAsAWhole whole = whole(read, List.of(asked(read, read.total(), 5)), 2);
        ContainerAsAWhole.Fixed fixed = whole.at(whole.choices().each().getFirst());
        assertNull(fixed.spread(List.of(new ObservedValue.Integer(0),
                        new ObservedValue.Integer(0)), null, 0, _ -> List.of(), _ -> null));
    }

    /**
     * A group read with the numbers of the whole fixed answers what it answers in a container
     * coming to them: one element of nought, in a container of one element fixed to come to a
     * hundred, is not at or above half of it — though alone it is half of what it comes to.
     */
    @Test
    void aGroupIsReadWithTheTotalFixedAndNotWithWhatItComesTo() {
        Read read = read();
        ContainerAsAWhole whole = whole(read, List.of(asked(read, read.total(), 100)), 1);
        ContainerAsAWhole.Fixed fixed = whole.at(whole.choices().each().getFirst());
        NumericTerm.ValueOf number = new NumericTerm.ValueOf(read.xs().element());
        // the total less twice the number is not above nought
        AStatementAtARow atOrAboveHalf = AStatementAtARow.of(new Proposition.Compared(
                new Relation.Affine(new LinearForm<>(ExactRatio.ZERO, Map.of(
                        new DecisionAtom.OfTheInput(read.total()), ExactRatio.ONE,
                        new DecisionAtom.OfTheInput(number), ExactRatio.of(-2))), Rel.GT),
                false), "counted", read.measuring());
        BorderQuantity.Observation alone = ElementValues.holding(read.xs(), read.reading(),
                new Type.ListOf(Type.INT), List.of(new ObservedValue.Integer(0)));
        assertInstanceOf(AStatementAtARow.Answer.Holds.class, atOrAboveHalf.at(alone),
                "the control: alone, nought is half of what it comes to");
        assertInstanceOf(AStatementAtARow.Answer.Fails.class, atOrAboveHalf.at(
                        CardinalityComposer.withNumbersBeside(alone, fixed.beside(Map.of()))),
                "read with the total fixed at a hundred");
        assertFalse(whole.admitsNone(read.measuring().region()),
                "and the container of none does not come to a hundred");
        assertTrue(whole(read, List.of(asked(read, read.total(), 0)), 1)
                        .admitsNone(read.measuring().region()),
                "where nought is asked, it does");
    }
}
