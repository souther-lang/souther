package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.carrier.Membership;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static souther.compiler.partition.QuantityFixtures.stands;

/**
 * Where a row is not read at a count of elements with a number added to it, everything that
 * stopped the reading is said: the number the row did not say and the container the walk could not
 * reach are two reasons, and a reader told one would fix it and be told the other next.
 */
class WhatStoppedACountAndTheNumberBesideItAreBothSaidTest {

    private static final String MODEL = """
            module g

            data Ok

            behavior counted : (xs: List<Int>, limit: Int) -> Ok
            """;

    @Test
    void theNumberAndTheContainerAreBothSaid() {
        BorderQuantity.Stands told = stands(countPlusLimit(),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(1)), unreadRow());

        BorderQuantity.Stands.CouldNotTell stopped =
                assertInstanceOf(BorderQuantity.Stands.CouldNotTell.class, told);
        assertEquals(2, stopped.why().size(), stopped.why().toString());
    }

    /** {@code #xs [limit >= element] + limit}, the count with the limit added to it. */
    private static BorderQuantity.HowMany countPlusLimit() {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL), souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        InputDomain input = InputDomain.of(sigs.get("counted"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none());
        Quantities measuring = input.quantities(rules);

        TermPath xs = pathIn(input, "xs");
        NumericTerm element = new NumericTerm.ValueOf(xs.element());
        NumericTerm limit = new NumericTerm.ValueOf(pathIn(input, "limit"));
        Map<Quantity, ExactRatio> atLeast = new LinkedHashMap<>();
        atLeast.put(new DecisionAtom.OfTheInput(limit), ExactRatio.ONE);
        atLeast.put(new DecisionAtom.OfTheInput(element), ExactRatio.ONE.negated());
        CountedElements counted = CountedElements.of("counted", new Quantity.HowManyMeet(
                new DecisionSubject.AnInput(xs),
                new Proposition.Compared(new Relation.Affine(
                        new LinearForm<>(ExactRatio.ZERO, atLeast), Rel.GE), true)), measuring,
                AnElementMeeting.UNREAD);
        Map<NumericTerm, ExactRatio> added = new LinkedHashMap<>();
        added.put(limit, ExactRatio.ONE);
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(limit, TermOrdersFixtures.itself(limit, Carrier.WHOLE));
        return new BorderQuantity.HowMany(counted, new LinearForm<>(ExactRatio.ZERO, added), on,
                Optional.empty());
    }

    private static TermPath pathIn(InputDomain input, String spelled) {
        return input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow();
    }

    /** A row whose limit is a value nothing could read, and whose container the walk cannot
     *  reach. */
    private static BorderQuantity.Observation unreadRow() {
        return new BorderQuantity.Observation() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return WalkResult.reached(
                        new ObservationAtPoint.Value(new ObservedValue.Unknown("no")));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }

            @Override
            public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
                return WalkResult.couldNotWalk();
            }
        };
    }
}
