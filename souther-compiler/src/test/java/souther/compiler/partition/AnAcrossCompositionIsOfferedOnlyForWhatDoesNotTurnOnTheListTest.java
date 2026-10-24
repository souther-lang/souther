package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The elements of the lists inside the elements of an outer list are chosen as one list and then
 * shared out over the lists, so a container is composed that way only for a statement whose answer
 * for an element is the same however they are shared. One that reads the outer element, or the
 * list holding the element, is a different statement for each sharing, and nothing is offered for
 * it: what is offered would be read in one list and written in another. And the ways of sharing
 * them out are offered within the room the count has for containers, not past it.
 */
class AnAcrossCompositionIsOfferedOnlyForWhatDoesNotTurnOnTheListTest {

    private static final String SOURCE = """
            module g

            data Forecast = { currency: String, amount: Int }

            data Desk = { floor: Int, forecasts: List<Forecast> }

            data Ok

            behavior counted : (ds: List<Desk>) -> Ok
            """;

    private static final TermPath DS = TermPath.of("ds");

    private static final TermPath FORECASTS = DS.element().then("forecasts");

    private static final TermPath CURRENCY = FORECASTS.element().then("currency");

    /** The forecast above nought. */
    private static Proposition amountAboveNought() {
        return above(FORECASTS.element().then("amount"));
    }

    /** The desk the forecast is in above nought. */
    private static Proposition floorAboveNought() {
        return above(DS.element().then("floor"));
    }

    private static Proposition above(TermPath place) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(place)),
                        ExactRatio.ONE)), Rel.GT), true);
    }

    @Test
    void aStatementOfTheForecastItselfIsComposedAcrossTheDesks() {
        assertInstanceOf(TermRealizations.Realization.Built.class,
                composed(amountAboveNought()),
                "the forecast above nought is that in any desk");
    }

    @Test
    void aStatementReadingTheDeskHoldingTheForecastIsNotComposedAcrossTheDesks() {
        assertInstanceOf(TermRealizations.Realization.Unexhausted.class,
                composed(new Proposition.All(List.of(amountAboveNought(), floorAboveNought()),
                        "both")),
                "the forecasts are shared out over desks that hold their own floors");
    }

    /**
     * Sharing the elements out over the desks offers as many rows as the room it is given and no
     * more, and says the figure that turned the rest away.
     */
    @Test
    void sharingTheElementsOutOffersNoMoreRowsThanItHasRoomFor() {
        Read read = read();
        TypeSymbol forecast = TypeSymbols.declared(new TypeKey("g", "Forecast"));
        List<ObservedValue> elements = List.of(forecastOf(forecast, "USD", 1),
                forecastOf(forecast, "EUR", 2));
        NestedContainersAddingUp nesting = new NestedContainersAddingUp(FORECASTS.element());

        TermRealizations.Realization roomy = nesting.holdingThe(read.desks(), List.of(),
                elements, read.measuring().region(), read.reading(), 4);
        int wanted = assertInstanceOf(TermRealizations.Realization.Built.class, roomy)
                .values().size();
        assertTrue(wanted > 1, "two elements are shared out over the desks in more than one way");
        assertFalse(roomy.shortfall().figures()
                .contains(CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED));

        TermRealizations.Realization tight = nesting.holdingThe(read.desks(), List.of(),
                elements, read.measuring().region(), read.reading(), 1);
        assertEquals(1, assertInstanceOf(TermRealizations.Realization.Built.class, tight)
                .values().size());
        assertTrue(tight.shortfall().figures()
                .contains(CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED));
    }

    /** And a value occurring as often as asked, spread over the desks, within the room too. */
    @Test
    void spreadingAValueOverTheDesksOffersNoMoreRowsThanItHasRoomFor() {
        Read read = read();
        TermPath amount = FORECASTS.element().then("amount");
        Carrier carrier = read.measuring().ordersOf(new NumericTerm.ValueOf(amount)).observed();
        NestedContainersAddingUp nesting = new NestedContainersAddingUp(amount);
        List<NestedContainersAddingUp.Counted> counted =
                List.of(new NestedContainersAddingUp.Counted(Count.of(7), 1));
        List<Place> others = List.of(Count.of(8), Count.of(9));

        TermRealizations.Realization roomy = nesting.alike(read.desks(), List.of(), counted,
                others, carrier, read.measuring().region(), read.reading(), 8);
        assertTrue(assertInstanceOf(TermRealizations.Realization.Built.class, roomy)
                .values().size() > 1, "the leaves are spread over the desks in more than one way");

        TermRealizations.Realization tight = nesting.alike(read.desks(), List.of(), counted,
                others, carrier, read.measuring().region(), read.reading(), 1);
        assertEquals(1, assertInstanceOf(TermRealizations.Realization.Built.class, tight)
                .values().size());
        assertTrue(tight.shortfall().figures()
                .contains(CompositionBudget.CONTAINERS_A_COUNT_IS_OFFERED));
    }

    private static ObservedValue forecastOf(TypeSymbol type, String currency, long amount) {
        return new ObservedValue.Constructed(type, Map.of("currency",
                new ObservedValue.Text(currency), "amount", new ObservedValue.Integer(amount)));
    }

    /** The input of {@link #SOURCE}, read: its desks, its numbers and its rules. */
    private record Read(Type desks, Quantities measuring, RuleReadingContext reading) {}

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
        return new Read(sigs.get("counted").inputs().getFirst().type(), input.quantities(rules),
                reading);
    }

    /** One different currency among the forecasts that meet {@code kept}, across the desks. */
    private static TermRealizations.Realization composed(Proposition kept) {
        Read read = read();
        Quantities measuring = read.measuring();
        RuleReadingContext reading = read.reading();
        Type desks = read.desks();

        Quantity count = Quantity.HowManyDifferentMeet.of(new DecisionSubject.AnInput(DS),
                new Quantity.TheValue.AtAPlace(new DecisionSubject.AnInput(CURRENCY)),
                new Quantity.HowManyDifferentMeet.Selection.OfEachElement(kept));
        RealizationTarget.ACount asked = new RealizationTarget.ACount(
                CountedElements.of("counted", count, measuring, AnElementMeeting.UNREAD));
        SequencedMap<RealizationTarget, AskedAt> demands = new LinkedHashMap<>();
        demands.put(asked, AskedAt.oneNumberOf(NumbersAskedFor.of(LevelRegion.point(
                new Level.OfTheQuantity(ExactRatio.ONE))), Count.of(1)));
        return CardinalityComposer.compose(desks, List.of(), List.of(asked), List.of(), demands,
                null, List.of(), measuring, measuring.region(), reading);
    }
}
