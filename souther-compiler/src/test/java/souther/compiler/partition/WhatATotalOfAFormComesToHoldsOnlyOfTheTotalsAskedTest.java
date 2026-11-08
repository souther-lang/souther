package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a total of a form of each element's places comes to as the total of the place and how many
 * there are is a fact about numbers, and a total of the place no row worked out is no number the
 * row holds: it is held to no order. Held to where an {@code Int} stops, it would leave out a row
 * whose total asked is worked out at every step and whose total of the place is past where it
 * stops.
 *
 * <p>The oracle is the row, worked out by hand: two elements at the greatest {@code Int} and at
 * two. Each less one is worked out, they come to the greatest {@code Int}, and the numbers
 * themselves come to two past it.
 */
class WhatATotalOfAFormComesToHoldsOnlyOfTheTotalsAskedTest {

    @Test
    void aRowWhoseTotalOfThePlaceIsPastWhereItStopsIsLeft() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module g

                data Line = { a: Int }
                data Ok

                behavior counted : (xs: List<Line>) -> Ok
                """), ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading = RuleReadingContext.unshared(rules,
                ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(compilation.db().ask(
                        new Bodies.DeclaredSignatures(module)).value().get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        TermPath xs = TermPath.of("xs");
        // a - 1 of each element, added up
        NumericTerm lessOne = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ComputedOccurrences(xs.element(), new ElementValue.Affine(
                        new LinearForm<>(ExactRatio.ONE.negated(), Map.of(
                                ElementProjection.ofFields(List.of("a")), ExactRatio.ONE))),
                        Type.INT, null),
                Type.INT, rules.inners(), rules.symbols());
        NumericTerm howMany = NumericTerm.TakenOf.asItStands(
                ValueName.Stdlib.operation("List", "length"), xs, input.typeAt(xs, rules),
                rules.inners(), rules.symbols());
        NumericTerm ofA = NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(xs.element().then("a")), Type.INT,
                rules.inners(), rules.symbols());
        SearchRegion region = input.quantities(rules).region();
        Endpoint seven = Endpoint.inclusive(Count.of(7));
        assertEquals(new NumericDomain.FormProjection.Within(new NumericDomain.Bounds(seven, seven)),
                region.given(Map.of(lessOne, Count.of(5), howMany, Count.of(2))).projectionOf(ofA),
                "the control: two elements each less one coming to five come to seven");
        assertTrue(region.given(Map.of(lessOne, Count.of(Long.MAX_VALUE), howMany, Count.of(2)))
                        .emptiness().isEmpty(),
                "the row of the greatest Int and two is left");
    }
}
