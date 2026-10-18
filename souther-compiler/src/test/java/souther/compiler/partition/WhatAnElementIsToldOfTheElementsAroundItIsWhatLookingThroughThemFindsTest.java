package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AsACompilationAllows;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a reading is told of the elements around the one it chose — whether that element is the
 * last to hold its sku, and whether an operation stopped before it — is what looking through the
 * elements for that reading alone finds: the walk each reading made for itself before what one
 * reading of an occurrence works out was kept for the others.
 *
 * <p>Over every order of up to three lines whose skus or whose flags were read, were not read
 * for one reason or another, or are no truth, beside an order with no lines, one with a line, and
 * one not read.
 */
class WhatAnElementIsToldOfTheElementsAroundItIsWhatLookingThroughThemFindsTest {

    private static final String MODEL = """
            module g

            data Line = { sku: String, open: Bool }

            data Order = { lines: List<Line> }

            behavior decide : (orders: List<Order>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final BehaviorInputs WHERE = new BehaviorInputs(List.of("orders"),
            List.of(new Type.ListOf(Type.ref(sym("Order")))), RuleReadings.ofSource(MODEL),
            POLICY);

    private static final TermPath ORDERS = TermPath.of("orders");

    private static final TermPath LINES = ORDERS.element().then("lines");

    private static final TermPath SKU = LINES.element().then("sku");

    private static final TermPath OPEN = LINES.element().then("open");

    private static final ObservedValue TRUNCATED =
            new ObservedValue.Truncated(Limits.DEFAULT.nodesFigure());

    private static final ObservedValue UNREADABLE = new ObservedValue.Unknown("no");

    @Test
    void whetherALineIsTheLastOfItsSkuIsWhatLookingAfterItFinds() {
        List<ObservedValue> skus = List.of(new ObservedValue.Text("A"),
                new ObservedValue.Text("B"), TRUNCATED, UNREADABLE);
        for (List<ObservedValue> lines : listsOf(skus)) {
            List<ObservedValue> written = new ArrayList<>();
            lines.forEach(sku -> written.add(line(sku, new ObservedValue.Bool(false))));
            for (ObservedValue beside : besides()) {
                for (BorderQuantity.Observation reading : readingsOf(order(written), beside)) {
                    assertEquals(lastnessLookedFor(reading), reading.lastToHold(LINES, SKU),
                            () -> written + " beside " + beside);
                }
            }
        }
    }

    @Test
    void whetherAnOperationStoppedBeforeALineIsWhatLookingBeforeItFinds() {
        AStatementAtARow stops = AStatementAtARow.of(
                new Proposition.Truth(new DecisionSubject.AnInput(OPEN), true), "decide", null);
        MetOnARow metOn = MetOnARow.of(new ElementsMetOn(
                List.of(new ElementsMetOn.Level.StopsAt(LINES,
                        new Proposition.Truth(new DecisionSubject.AnInput(OPEN), true))),
                new Proposition.Always(true)), "decide", null);
        List<ObservedValue> flags = List.of(new ObservedValue.Bool(true),
                new ObservedValue.Bool(false), TRUNCATED, UNREADABLE, new ObservedValue.Integer(1));
        for (List<ObservedValue> lines : listsOf(flags)) {
            List<ObservedValue> written = new ArrayList<>();
            lines.forEach(open -> written.add(line(new ObservedValue.Text("A"), open)));
            for (ObservedValue beside : besides()) {
                for (BorderQuantity.Observation reading : readingsOf(order(written), beside)) {
                    assertEquals(stoppedBeforeLookedFor(stops, reading), metOn.at(reading),
                            () -> written + " beside " + beside);
                }
            }
        }
    }

    /**
     * Whether the line {@code reading} chose is the last of its sku, looking at every value at the
     * sku the row wrote under the order it chose: the line's own last, and every one after it.
     */
    private static BorderQuantity.Lastness lastnessLookedFor(BorderQuantity.Observation reading) {
        StandingAtAPoint.WalkOfARow walk = (StandingAtAPoint.WalkOfARow) reading;
        Map<TermPath, Integer> chosen = walk.chosen();
        Integer mine = chosen.get(LINES);
        if (mine == null || !walk.walk().at(SKU).walked()) {
            return new BorderQuantity.Lastness.CouldNotTell(ReadingGap.COULD_NOT_WALK);
        }
        List<BehaviorInputs.Occurrence> values = walk.walk().at(SKU).values();
        ObservedValue held = null;
        for (BehaviorInputs.Occurrence each : values) {
            if (agreesBeside(each, chosen) && mine.equals(each.at().elementAt(LINES))) {
                held = each.value();
            }
        }
        if (held == null) {
            return new BorderQuantity.Lastness.CouldNotTell(ReadingGap.COULD_NOT_WALK);
        }
        if (ReadingGap.ofAComparisonOf(held) != null) {
            return new BorderQuantity.Lastness.CouldNotTell(ReadingGap.ofAComparisonOf(held));
        }
        ReadingGap notTold = null;
        for (BehaviorInputs.Occurrence each : values) {
            Integer taken = each.at().elementAt(LINES);
            if (!agreesBeside(each, chosen) || taken == null || taken <= mine) {
                continue;
            }
            ReadingGap laterNotRead = ReadingGap.ofAComparisonOf(each.value());
            if (laterNotRead != null) {
                notTold = notTold != null ? notTold : laterNotRead;
            } else if (held.equals(each.value())) {
                return new BorderQuantity.Lastness.NotLast();
            }
        }
        return notTold != null ? new BorderQuantity.Lastness.CouldNotTell(notTold)
                : new BorderQuantity.Lastness.Last();
    }

    /**
     * Whether no line before the one {@code reading} chose stopped the operation, asking
     * {@code stops} of each line before it in order: one that stops it settles that it did, and
     * what could not be told of each before it is what this could not tell.
     */
    private static AStatementAtARow.Answer stoppedBeforeLookedFor(
            AStatementAtARow stops, BorderQuantity.Observation reading) {
        if (!(reading.among(LINES) instanceof WalkResult.Reached<BorderQuantity.Among>(
                BorderQuantity.Among among))) {
            return new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
        }
        if (among.chosen() == null) {
            return AStatementAtARow.Answer.HOLDS;
        }
        if (!(reading.elementsOf(LINES) instanceof WalkResult.Reached<List<BorderQuantity.AnElement>>(
                List<BorderQuantity.AnElement> elements))) {
            return new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
        }
        Set<ReadingGap> why = new LinkedHashSet<>();
        for (BorderQuantity.AnElement one : elements) {
            if (one.element() >= among.chosen()) {
                break;
            }
            switch (stops.at(one.reading())) {
                case AStatementAtARow.Answer.Holds _ -> {
                    return AStatementAtARow.Answer.FAILS;
                }
                case AStatementAtARow.Answer.Fails _ -> { }
                case AStatementAtARow.Answer.CouldNotTell(var stopped) -> why.addAll(stopped);
            }
        }
        return why.isEmpty() ? AStatementAtARow.Answer.HOLDS
                : new AStatementAtARow.Answer.CouldNotTell(why);
    }

    /** Whether {@code each} was reached through what {@code chosen} names of every container
     *  but the lines. */
    private static boolean agreesBeside(BehaviorInputs.Occurrence each,
                                        Map<TermPath, Integer> chosen) {
        for (Map.Entry<TermPath, Integer> picked : chosen.entrySet()) {
            Integer taken = each.at().elementAt(picked.getKey());
            if (!picked.getKey().equals(LINES) && taken != null
                    && !taken.equals(picked.getValue())) {
                return false;
            }
        }
        return true;
    }

    /** Every reading of a row holding {@code first} and {@code second}, over every line. */
    private static List<BorderQuantity.Observation> readingsOf(ObservedValue first,
                                                               ObservedValue second) {
        NumericTerm.ValueOf sku = new NumericTerm.ValueOf(SKU);
        return StandingAtAPoint.readings(WHERE,
                new ObservedInputs(List.of(new ObservedValue.Sequence(List.of(first, second))),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()),
                new BorderQuantity.OfACoordinate("decide", sku,
                        TermOrdersFixtures.itself(sku, Carrier.TEXT))).tried();
    }

    /** An order with no lines, one with a line, and one not read. */
    private static List<ObservedValue> besides() {
        return List.of(order(List.of()),
                order(List.of(line(new ObservedValue.Text("A"), new ObservedValue.Bool(true)))),
                TRUNCATED);
    }

    /** Every list of up to three of {@code palette}, in every order and with repeats. */
    private static List<List<ObservedValue>> listsOf(List<ObservedValue> palette) {
        List<List<ObservedValue>> out = new ArrayList<>();
        out.add(List.of());
        List<List<ObservedValue>> shorter = List.of(List.of());
        for (int length = 1; length <= 3; length++) {
            List<List<ObservedValue>> longer = new ArrayList<>();
            for (List<ObservedValue> each : shorter) {
                for (ObservedValue one : palette) {
                    List<ObservedValue> grown = new ArrayList<>(each);
                    grown.add(one);
                    longer.add(grown);
                }
            }
            out.addAll(longer);
            shorter = longer;
        }
        return out;
    }

    private static ObservedValue order(List<ObservedValue> lines) {
        return new ObservedValue.Constructed(sym("Order"),
                Map.of("lines", new ObservedValue.Sequence(lines)));
    }

    private static ObservedValue line(ObservedValue sku, ObservedValue open) {
        return new ObservedValue.Constructed(sym("Line"), Map.of("sku", sku, "open", open));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
