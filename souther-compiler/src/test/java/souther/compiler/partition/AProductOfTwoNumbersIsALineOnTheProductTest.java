package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.OfferedAtTheLines;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What two whole numbers of the input come to multiplied is a number of its own, and a rule about
 * it is a line on that number and on neither factor.
 *
 * <p>{@code price * quantity >= 1000} relates the two: fixing either leaves a line on the other at
 * the level over it, which moves with the value fixed. A row at the line is a pair whose product is
 * the level. And a factor's own values divide the rule where they settle it whatever the other is:
 * at nought the product is nought, so nought is a class of each factor, and every other value
 * leaves the other reaching both sides of the level over it.
 */
class AProductOfTwoNumbersIsALineOnTheProductTest {

    private static final String PRICE_AND_QUANTITY = "price: Int, quantity: Int";

    /** The line is on the product, and nought is a class of each factor. */
    @Test
    void aProductIsALineOnTheProductAndNoughtIsAClassOfEachFactor() {
        Compilation compilation = compiled("", PRICE_AND_QUANTITY, "price * quantity >= 1000");
        assertEquals(List.of("1000"), bordersOf(linesOf(compilation)));
        Map<String, List<String>> classes = classesOf(measured(compilation));
        assertEquals(List.of("price/= 0", "price//= 0"), classes.get("price"), classes.toString());
        assertEquals(List.of("quantity/= 0", "quantity//= 0"), classes.get("quantity"),
                classes.toString());
    }

    /** A row the line is owed is a pair whose product is the level the row is labelled with. */
    @Test
    void aRowAtTheLineIsAPairWhoseProductIsTheLevel() {
        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows(linesOf(compiled("", PRICE_AND_QUANTITY,
                "price * quantity >= 1000")))) {
            for (String label : row.labels()) {
                if (label.startsWith("price * quantity = ")) {
                    long level = Long.parseLong(label.substring(label.lastIndexOf(' ') + 1));
                    long price = Long.parseLong(row.inputs().get(0));
                    long quantity = Long.parseLong(row.inputs().get(1));
                    assertEquals(level, Math.multiplyExact(price, quantity),
                            label + " at " + row.inputs());
                    labels.add(label);
                }
            }
        }
        assertEquals(List.of("price * quantity = 1000", "price * quantity = 999"),
                labels.stream().sorted().toList(), "the line and the value below it");
    }

    /**
     * A level only one pair of the factors' values multiplies to is still reached, by the divisor
     * the walk tries: with the factors held at seven or more, 49 is only seven times seven.
     */
    @Test
    void aLevelIsReachedByThePairItsDivisorsMake() {
        String prelude = """
                data AtLeastSeven = Int
                    invariant value >= 7
                """;
        List<String> labels = new ArrayList<>();
        for (Row row : certifiedRows(linesOf(compiled(prelude, "a: AtLeastSeven, b: AtLeastSeven",
                "a.value * b.value == 49")))) {
            for (String label : row.labels()) {
                if (label.endsWith(" = 49")) {
                    assertEquals(List.of("AtLeastSeven(7)", "AtLeastSeven(7)"), row.inputs(),
                            label);
                    labels.add(label);
                }
            }
        }
        assertEquals(List.of("a * b = 49"), labels);
    }

    /**
     * One product however it is written: factors either way round, the comparison either way
     * round, or behind a name. The line is at one level and the classes are one partition.
     */
    @Test
    void aProductIsOneLineHoweverItIsWritten() {
        Map<List<String>, String> spellings = new LinkedHashMap<>();
        spellings.put(List.of("guard price * quantity >= 1000 else No", "Ok"), "written");
        spellings.put(List.of("guard quantity * price >= 1000 else No", "Ok"), "turned round");
        spellings.put(List.of("guard 1000 <= price * quantity else No", "Ok"), "faced the other way");
        spellings.put(List.of("let amount = price * quantity", "guard amount >= 1000 else No", "Ok"),
                "named");
        List<String> borders = null;
        Map<String, List<String>> classes = null;
        for (Map.Entry<List<String>, String> each : spellings.entrySet()) {
            Compilation compilation = compiled("", PRICE_AND_QUANTITY, each.getKey(), "");
            List<String> theseBorders = bordersOf(linesOf(compilation));
            Map<String, List<String>> theseClasses = classesOf(measured(compilation));
            if (borders == null) {
                borders = theseBorders;
                classes = theseClasses;
            }
            assertEquals(borders, theseBorders, each.getValue());
            assertEquals(classes, theseClasses, each.getValue());
        }
    }

    /**
     * Factors held from one to a hundred thousand: from a thousand on, either one holds the rule
     * whatever the other is, so a thousand is where each factor's values part, and below it the
     * other reaches both sides of the level over it.
     */
    @Test
    void aFactorFarFromNoughtSettlesTheRuleAndIsAClassOfItsOwn() {
        String prelude = """
                data Price = Int
                    invariant value >= 1 && value <= 100000

                data Quantity = Int
                    invariant value >= 1 && value <= 100000
                """;
        Map<String, List<String>> classes = classesOf(measured(compiled(prelude,
                "price: Price, quantity: Quantity", "price.value * quantity.value >= 1000")));
        assertEquals(List.of("price/1 <= x < 1000", "price/1000 <= x <= 100000"),
                classes.get("price"), classes.toString());
        assertEquals(List.of("quantity/1 <= x < 1000", "quantity/1000 <= x <= 100000"),
                classes.get("quantity"), classes.toString());
    }

    /**
     * A product of one number with itself or of three numbers is not read as one, and neither is
     * a product of three with arithmetic before or after it, which the run does in the type: at
     * {@code price} of two to the sixty-second, {@code price * quantity * price * 2} stops the run
     * for every {@code quantity} above nought, where a product held against five hundred would
     * come out true. Each is named as a product.
     */
    @Test
    void aProductThisDoesNotReadIsNamedAsAProduct() {
        for (String condition : List.of("price * price >= 1000",
                "price * quantity * price >= 1000", "price * quantity * price * 2 >= 1000",
                "price * quantity * price - 5 >= 995",
                "0 - price * quantity * price <= 0 - 1000")) {
            Compilation compilation = compiled("", PRICE_AND_QUANTITY, condition);
            assertEquals(List.of(), bordersOf(linesOf(compilation)), condition);
            assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    reasonsOf(measured(compilation)), condition);
        }
    }

    /**
     * A product beside other numbers relates the numbers of both, and is read where a number
     * stands in the product and beside it: {@code a - a * b} is {@code a} at one value and
     * {@code 1 - b} at another, and a row for each side of the line is the pair of inputs that
     * makes it.
     */
    @Test
    void aProductBesideOtherNumbersIsReadAndLeavesNoPlaceUnread() {
        for (String condition : List.of("a * b + c >= 1000", "a * b <= c", "a - a * b <= c",
                "a * b + a <= c", "Int.max(0, a - a * b) <= c", "c - b * a >= 5")) {
            Compilation compilation = compiled("", "a: Int, b: Int, c: Int", condition);
            PartitionEvidence measured = measured(compilation);
            List<BorderAssessment> lines = linesOf(compilation);
            assertTrue(!lines.isEmpty(), condition);
            for (BorderAssessment line : lines) {
                if (!line.axis().contains("*")) {
                    continue;
                }
                assertTrue(!certifiedRows(List.of(line)).isEmpty(),
                        condition + " has no row for " + line.axis() + " @ " + line.value());
            }
            assertTrue(!reasonsOf(measured).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    condition + ": " + reasonsOf(measured));
        }
    }

    private static final String MONEY_AND_RATE = """
            data Money = Decimal
                invariant value >= 0.0m

            data Rate = Decimal
                invariant value >= 0.0m
            """;

    /**
     * The product of two decimals is a number of its own beside the other numbers of a comparison,
     * as one of whole numbers is: a rule over {@code g * (1 - r)} is read, every position is shown
     * to reach it, and a row is built at a point of the line by the numbers that make the product.
     */
    @Test
    void aProductOfDecimalsBesideOtherNumbersIsReadAndALineIsReachedByARow() {
        for (String condition : List.of(
                "Decimal.compare(Decimal.multiply(g.value, r.value), c.value) <= 0",
                "Decimal.compare(Decimal.multiply(g.value, r.value), 5.0m) <= 0",
                "Decimal.compare(Decimal.max(0.0m, Decimal.multiply(g.value, r.value)),"
                        + " c.value) <= 0",
                "Decimal.compare(Decimal.subtract(g.value,"
                        + " Decimal.multiply(g.value, r.value)), c.value) <= 0",
                "Decimal.compare(Decimal.max(0.0m, Decimal.subtract(g.value,"
                        + " Decimal.multiply(g.value, r.value))), c.value) <= 0")) {
            Compilation compilation = compiled(MONEY_AND_RATE, "g: Money, r: Rate, c: Money",
                    condition);
            assertEquals(List.of(), unreadReasonsOf(measured(compilation)), condition);
            List<Row> rows = certifiedRows(linesOf(compilation));
            assertTrue(!rows.isEmpty(), condition);
        }
    }

    /**
     * Where the declarations leave the factor beside the number alone no place it comes to one, the
     * number alone stands at the value over what the factor comes to inside the run: a rate
     * strictly between nought and one is at a half, and a price of two pennies leaves a penny.
     */
    @Test
    void aFactorThatCannotBeOneIsHeldInsideTheRunItIsLeft() {
        String prelude = """
                data Price = Decimal
                    invariant value >= 0.00m

                data Rate = Decimal
                    invariant value > 0.00m && value < 1.00m
                """;
        Compilation compilation = compiled(prelude, "price: Price, rate: Rate",
                "Decimal.compare(Decimal.subtract(price.value,"
                        + " Decimal.multiply(price.value, rate.value)), 0.01m) >= 0");
        List<BorderAssessment> lines = linesOf(compilation);
        assertTrue(lines.stream().anyMatch(line -> line.axis().contains("*")), describe(lines));
        for (BorderAssessment line : lines) {
            if (line.axis().contains("*")) {
                assertEquals(List.of(), pointsWithNoRow(line));
            }
        }
        assertTrue(certifiedRows(lines).stream().anyMatch(row ->
                row.inputs().equals(List.of("Price(0.02m)", "Rate(0.5m)"))),
                certifiedRows(lines).toString());
    }

    /**
     * A whole number made a decimal is a number a row holds as it is, so a decimal operation over
     * it is one a row is asked to get past: every position of the rule is shown to reach it.
     */
    @Test
    void aWholeNumberMadeADecimalIsMultipliedAsAnyDecimalIs() {
        PartitionEvidence measured = measured(compiled(MONEY_AND_RATE, "a: Int, r: Rate, c: Money",
                "Decimal.compare(Decimal.subtract(Decimal.fromInt(a),"
                        + " Decimal.multiply(Decimal.fromInt(a), r.value)), c.value) <= 0"));
        assertEquals(List.of(), unreadReasonsOf(measured));
    }

    /**
     * A whole number made a decimal is multiplied as a decimal is, and a total of the products of
     * two maps' values made one is the number that carries the product: the line is read and
     * reached by a row whose maps hold the entries the total is made of.
     */
    @Test
    void aTotalMadeADecimalAndMultipliedIsReadAndReached() {
        for (String net : List.of("Decimal.max(0.0m, Decimal.subtract(gross, fee))",
                "Decimal.subtract(gross, fee)")) {
            String model = """
                    module demo

                    data Ok
                    data No
                    data Money = Decimal
                        invariant value >= 0.0m

                    let lineValue (sku: String, quantity: Int, prices: Map<String, Int>): Int = {
                        let price = Map.get(sku, prices) |> Option.withDefault(0)
                        price * quantity
                    }

                    behavior f : (agreed: Map<String, Int>, prices: Map<String, Int>, c: Money,
                                  rate: Decimal) -> Ok | No
                    let f (agreed, prices, c, rate) = {
                        let gross = Decimal.fromInt(Map.fold((acc, sku, quantity) ->
                            acc + lineValue(sku, quantity, prices), 0, agreed))
                        let fee = Decimal.multiply(gross, rate)
                        let net = %s
                        guard Decimal.compare(net, c.value) <= 0 else No
                        Ok
                    }
                    """.formatted(net);
            Compilation compilation = Compilation.ofSource(model, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), unreadReasonsOf(measured(compilation)), net);
            List<BorderAssessment> lines = linesOf(compilation);
            assertTrue(lines.stream().anyMatch(line -> line.axis().contains("*")),
                    net + ": " + describe(lines));
            for (BorderAssessment line : lines) {
                if (line.axis().contains("*")) {
                    assertEquals(List.of(), pointsWithNoRow(line), net);
                }
            }
        }
    }

    /**
     * What a way states of a total alone is what it states of the one element the total is of:
     * under {@code 0 <= List.sum(xs)} the total takes every value from nought, as the element
     * does, so a rule on the total beside another number is shown to reach every value.
     */
    @Test
    void aBoundTheWayStatesOfATotalAloneLeavesTheTotalEveryValueWithinIt() {
        assertEquals(List.of(), unreadReasonsOf(measured(compiled("", "xs: List<Int>, c: Int",
                "Int.max(0, List.sum(xs)) <= c"))));
        Compilation fold = Compilation.ofSource("""
                module demo

                data Ok
                data No

                behavior f : (ys: Map<String, Int>, c: Int) -> Ok | No
                let f (ys, c) = {
                    guard Int.max(0, Map.fold((acc, key, value) -> acc + value, 0, ys)) <= c else No
                    Ok
                }
                """, "Main");
        fold.measure(Adequacy.Asked.fullReport());
        fold.answerEverything();
        assertEquals(List.of(), unreadReasonsOf(measured(fold)));
    }

    /**
     * A product is held at a value inside the run only where one over what the factor comes to
     * there is a decimal. Between two tenths and four tenths the middle is three tenths and
     * leaves seven tenths, over which a hundredth is no decimal: the number alone would not stand
     * at every value it is claimed to. Between a quarter and three quarters the middle is a half,
     * and twice any decimal is one.
     */
    @Test
    void aFactorIsHeldInsideTheRunOnlyWhereOneOverWhatItComesToIsADecimal() {
        NumericTerm price = new NumericTerm.ValueOf(TermPath.of("price"));
        NumericTerm rate = new NumericTerm.ValueOf(TermPath.of("rate"));
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(LinearForm.atom(price),
                new LinearForm<>(ExactRatio.ONE, Map.of(rate, ExactRatio.of(-1))));
        assertEquals(ExactRatio.ZERO, product.atAValue().at());

        NumericTerm.ProductOf aHalf = product.standingWhereTheDeclarationsAdmit(
                between("0.25", "0.75"));
        assertEquals(ExactRatio.of(new BigDecimal("0.5")), aHalf.atAValue().at());
        assertEquals(ExactRatio.of(new BigDecimal("0.5")), aHalf.atAValue().scale());

        assertEquals(product, product.standingWhereTheDeclarationsAdmit(between("0.2", "0.4")));
        // Four fifths over one is a number a row of few places has five more places in: a
        // decimal, but one the row was not built with.
        assertEquals(product, product.standingWhereTheDeclarationsAdmit(between("0.1", "0.3")));
        // Three quarters leaves a quarter, and four times a value has the places the value has.
        assertEquals(ExactRatio.of(new BigDecimal("0.75")),
                product.standingWhereTheDeclarationsAdmit(between("0.7", "0.8")).atAValue().at());
    }

    /**
     * A run times a scale has the ends it is written with, and none where an end would need more
     * places than a decimal holds: half of the least scale there is, is no decimal.
     */
    @Test
    void aRunTimesAScaleHasNoEndPastWhatADecimalHolds() {
        NumericDomain.Bounds fromTheLeast = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal("1E-2147483647"))), null);
        ExactRatio aHalf = ExactRatio.of(new BigDecimal("0.5"));
        assertEquals(null, fromTheLeast.timesEach(aHalf));
        assertTrue(fromTheLeast.timesEach(ExactRatio.of(2)) != null);
    }

    /**
     * The number beside the one alone stands inside its run on its own order: a rate of whole
     * numbers strictly between nought and three has a middle of one and a half, which no whole
     * number is, and strictly between nought and four a middle of two.
     */
    @Test
    void aNumberOfWholeNumbersIsHeldInsideTheRunOnlyAtAWholeNumber() {
        NumericTerm price = new NumericTerm.ValueOf(TermPath.of("price"));
        NumericTerm rate = new NumericTerm.ValueOf(TermPath.of("rate"));
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(LinearForm.atom(price),
                new LinearForm<>(ExactRatio.ONE, Map.of(rate, ExactRatio.of(-1))));
        assertEquals(product, product.standingWhereTheDeclarationsAdmit(
                wholeBetween("0", "3")));
        assertEquals(ExactRatio.of(2), product.standingWhereTheDeclarationsAdmit(
                wholeBetween("0", "4")).atAValue().at());
    }

    /** The same, with {@code rate} counted in whole numbers and {@code price} in decimals. */
    private static NumericTerm.ProductOf.Declared wholeBetween(String low, String high) {
        NumericTerm.ProductOf.Declared dense = between(low, high);
        return new NumericTerm.ProductOf.Declared() {
            @Override
            public NumericDomain.Bounds runOf(NumericTerm number) {
                return dense.runOf(number);
            }

            @Override
            public boolean isDense(NumericTerm number) {
                return !number.toString().equals("rate");
            }
        };
    }

    /** The declarations leave {@code rate} the values strictly between {@code low} and
     *  {@code high}, and every number is counted on decimals. */
    private static NumericTerm.ProductOf.Declared between(String low, String high) {
        return new NumericTerm.ProductOf.Declared() {
            @Override
            public NumericDomain.Bounds runOf(NumericTerm number) {
                return number.toString().equals("rate")
                        ? new NumericDomain.Bounds(
                                Endpoint.exclusive(Count.of(new BigDecimal(low))),
                                Endpoint.exclusive(Count.of(new BigDecimal(high))))
                        : null;
            }

            @Override
            public boolean isDense(NumericTerm number) {
                return true;
            }
        };
    }
    /**
     * What is claimed of a construction that stops a run is what a run does: the row that gives
     * a negative rate is refused when it is applied, and the one that gives a rate of a half is
     * not.
     */
    @Test
    void theConstructionThatStopsForSomeRateStopsARowThatGivesOne() {
        String model = """
                module demo

                data Refund = Decimal
                    invariant value >= 0.0m
                data Money = Decimal
                    invariant value >= 0.0m
                data Plan = { fee: Refund, within: Bool }

                behavior f : (gross: Money, rate: Decimal, c: Money) -> Plan
                    constructs Plan, Refund
                let f (gross, rate, c) = {
                    let fee = Decimal.multiply(gross.value, rate)
                    Plan {
                        fee = Refund(Decimal.min(fee, gross.value)),
                        within = Decimal.compare(Decimal.subtract(gross.value, fee), c.value) <= 0
                    }
                }

                example f
                    | "a half" : (Money(10.0m), 0.5m, Money(100.0m))
                        -> Plan { fee = Refund(5.0m), within = true }
                    | "a negative rate" : (Money(10.0m), -0.5m, Money(100.0m))
                        -> Plan { fee = Refund(0.0m), within = true }
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String human = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).toString();
        assertTrue(human.contains("1 row does not hold"), human);
        assertTrue(human.contains("a negative rate"), human);
        assertTrue(!human.contains("a half is") && !human.contains("a half ("), human);
    }

    /**
     * A construction worked out before the comparison that stops a run for some rate keeps the
     * comparison from being shown reached: {@code Refund(Decimal.min(fee, gross))} is refused
     * for a negative rate, the minimum being the fee, so a row with that rate never gets to the
     * comparison and the positions are not shown to.
     */
    @Test
    void aConstructionBeforeTheComparisonThatStopsForSomeRateKeepsItNotShownReached() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Refund = Decimal
                    invariant value >= 0.0m
                data Money = Decimal
                    invariant value >= 0.0m
                data Plan = { fee: Refund, within: Bool }

                behavior f : (gross: Money, rate: Decimal, c: Money) -> Plan
                    constructs Plan, Refund
                let f (gross, rate, c) = {
                    let fee = Decimal.multiply(gross.value, rate)
                    Plan {
                        fee = Refund(Decimal.min(fee, gross.value)),
                        within = Decimal.compare(Decimal.subtract(gross.value, fee), c.value) <= 0
                    }
                }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE),
                unreadReasonsOf(measured(compilation)));
    }

    /**
     * A construction of a number held to at least nought by the operation that made it stops no
     * run: {@code Refund(Decimal.max(0.0m, x))} is told so whatever {@code x} is, and the
     * comparison after it is not kept from being shown reached.
     */
    @Test
    void aConstructionOfAMaximumWithNoughtStopsNoRun() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Refund = Decimal
                    invariant value >= 0.0m
                data Money = Decimal
                    invariant value >= 0.0m
                data Plan = { fee: Refund, within: Bool }

                behavior f : (gross: Money, rate: Decimal, c: Money) -> Plan
                    constructs Plan, Refund
                let f (gross, rate, c) = {
                    let fee = Decimal.multiply(gross.value, rate)
                    let net = Decimal.max(0.0m, Decimal.subtract(gross.value, fee))
                    Plan {
                        fee = Refund(net),
                        within = Decimal.compare(net, c.value) <= 0
                    }
                }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).map(each -> each.diagnostic().code()).toList());
        assertEquals(List.of(), unreadReasonsOf(measured(compilation)));
    }

    /**
     * What the library says of the larger of two is held to the clauses of the type it is made
     * into: at nought or above is not above nought, so {@code Positive(Decimal.max(0.0m, x))} may
     * still stop a run, for an {@code x} at nought or below.
     */
    @Test
    void aMaximumWithNoughtIsNoProofOfAnythingAboveNought() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Positive = Decimal
                    invariant value > 0.0m
                data Plan = { p: Positive, within: Bool }

                behavior f : (x: Decimal, c: Decimal) -> Plan
                    constructs Plan, Positive
                let f (x, c) = {
                    let net = Decimal.max(0.0m, x)
                    Plan {
                        p = Positive(net),
                        within = Decimal.compare(net, c) <= 0
                    }
                }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE),
                unreadReasonsOf(measured(compilation)));
    }

    /**
     * What the argument of the maximum is worked out with still stops a run when it can: the
     * construction of a number at nought or above says nothing of the sum under it.
     */
    @Test
    void aMaximumWithNoughtLeavesTheOperationsUnderItAsTheyWere() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Count = Int
                    invariant value >= 0
                data Plan = { n: Count, within: Bool }

                behavior f : (a: Int, b: Int, c: Int) -> Plan
                    constructs Plan, Count
                let f (a, b, c) = {
                    let net = Int.max(0, a + b)
                    Plan {
                        n = Count(net),
                        within = net <= c
                    }
                }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                unreadReasonsOf(measured(compilation)));
    }

    /**
     * The shape of a refund plan: the total of the agreed lines at their unit prices, a fee taken
     * off it, the rest held at nought or above, and compared with what was invoiced. Only the
     * construction that really stops keeps the comparison from being shown reached, and a row
     * past the invoiced amount is offered.
     */
    @Test
    void aRefundPlanIsStoppedOnlyByTheConstructionThatCanStopAndOffersARowPastTheInvoice() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Sku = String
                    invariant String.length(value) >= 1
                data Rma = String
                    invariant String.matches("RMA-[0-9]{8}", value)
                data InvoiceNo = String
                    invariant String.matches("INV-[0-9]{4}-[0-9]{6}", value)
                data Amount = Decimal
                    invariant value >= 0.0m
                data Refund = Decimal
                    invariant value >= 0.0m
                data Accepted = { rma: Rma, skus: Set<Sku>, daysSinceDispatch: Int }
                data Reconciliation =
                    { agreed: Map<Sku, Int>
                    , declaredOnly: Map<Sku, Int>
                    , receivedOnly: Map<Sku, Int>
                    , inDispute: Int
                    }
                data RefundPlan =
                    { rma: Rma
                    , invoiceNo: InvoiceNo
                    , refund: Refund
                    , restockingFee: Refund
                    , withinInvoiced: Bool
                    , repeatReturn: Bool
                    , recentRmas: List<Rma>
                    }

                let lineValue (sku: Sku, quantity: Int, unitPrices: Map<Sku, Int>): Int = {
                    let price = Map.get(sku, unitPrices) |> Option.withDefault(0)
                    price * quantity
                }

                let agreedValue (reconciliation: Reconciliation, unitPrices: Map<Sku, Int>): Int =
                    Map.fold((acc, sku, quantity) -> acc + lineValue(sku, quantity, unitPrices), 0,
                             reconciliation.agreed)

                behavior f : (accepted: Accepted, reconciliation: Reconciliation,
                               unitPrices: Map<Sku, Int>, invoiceNo: InvoiceNo,
                               invoicedGross: Amount, restockingRate: Decimal,
                               history: List<Rma>, previousSkus: List<Sku>) -> RefundPlan
                    constructs RefundPlan, Refund
                let f (accepted, reconciliation, unitPrices, invoiceNo, invoicedGross,
                       restockingRate, history, previousSkus) = {
                    let gross = Decimal.fromInt(agreedValue(reconciliation, unitPrices))
                    let fee = Decimal.multiply(gross, restockingRate)
                    let net = Decimal.max(0.0m, Decimal.subtract(gross, fee))
                    RefundPlan {
                        rma = accepted.rma,
                        invoiceNo = invoiceNo,
                        refund = Refund(net),
                        restockingFee = Refund(Decimal.min(fee, gross)),
                        withinInvoiced = Decimal.compare(net, invoicedGross.value) <= 0,
                        repeatReturn = Set.fold((acc, sku) -> acc || List.contains(sku, previousSkus),
                                                false, accepted.skus),
                        recentRmas = List.take(3, List.reverse(history))
                    }
                }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(unreadReasonsOf(measured(compilation))
                        .contains(UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE),
                "Refund(Decimal.min(fee, gross)) stops a run, for a negative rate");
        Generator.GenerationResult offered = OfferedAtTheLines.of(
                compilation, compilation.modules().get(0), "f");
        List<String> beyond = offered.rows().stream()
                .filter(row -> row.purposes().toString().contains("[ForAPoint[label=0 < List.sum"))
                .map(row -> row.inputs().stream().map(each -> each.text()).toList().toString())
                .toList();
        assertEquals(List.of("[Accepted { rma = Rma(\"RMA-00000000\"), skus = [], "
                        + "daysSinceDispatch = 0 }, Reconciliation { agreed = [(Sku(\"x\"), 1)], "
                        + "declaredOnly = [], receivedOnly = [], inDispute = 0 }, "
                        + "[(Sku(\"x\"), 1)], InvoiceNo(\"INV-0000-000000\"), Amount(0m), 0m, [], []]"),
                beyond, "one unit at one, nothing taken off, and nothing invoiced");
    }

    /** A decimal times itself is no product of two numbers apart, and is named as a product. */
    @Test
    void aDecimalTimesItselfIsStillNamedAsAProduct() {
        PartitionEvidence measured = measured(compiled(MONEY_AND_RATE, "g: Money, c: Money",
                "Decimal.compare(Decimal.multiply(g.value, g.value), c.value) <= 0"));
        assertTrue(reasonsOf(measured).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                reasonsOf(measured).toString());
    }

    /** A number times itself is no product of two numbers apart, and is named as a product. */
    @Test
    void aNumberTimesItselfBesideOtherNumbersIsStillNamedAsAProduct() {
        for (String condition : List.of("a * a + c >= 1000", "a - a * a <= c")) {
            PartitionEvidence measured = measured(
                    compiled("", "a: Int, c: Int", condition));
            assertTrue(reasonsOf(measured).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    condition + ": " + reasonsOf(measured));
        }
    }

    /**
     * A product with arithmetic written around it is read, the multiplication still told as the
     * operation it is: a factor weighed, negated or moved, and a product weighed, moved or
     * negated, each draw a line on the product at the level the arithmetic moves it to.
     */
    @Test
    void aProductWithArithmeticAroundItIsReadAtTheLevelTheArithmeticMovesItTo() {
        Map<String, String> level = new LinkedHashMap<>();
        level.put("2 * price * quantity >= 1000", "1000");
        level.put("(0 - price) * quantity >= 1000", "-1000");
        level.put("(price + 1) * quantity >= 1000", "1000");
        level.put("price * quantity * 2 >= 1000", "1000");
        level.put("price * quantity - 5 >= 995", "1000");
        level.put("0 - price * quantity <= 0 - 1000", "1000");
        for (Map.Entry<String, String> each : level.entrySet()) {
            Compilation compilation = compiled("", PRICE_AND_QUANTITY, each.getKey());
            assertEquals(List.of(), unreadReasonsOf(measured(compilation)), each.getKey());
            assertTrue(linesOf(compilation).stream().anyMatch(line -> line.axis().contains("*")
                            && line.value().equals(each.getValue())),
                    each.getKey() + ": " + describe(linesOf(compilation)));
        }
    }

    /**
     * Factors a rule of the value they sit in relates are tied, and what one reaches beside the
     * other is not shown: the line is drawn, and neither factor is divided or shown undivided.
     * The rule relating them is a relation of its own, and says so.
     */
    @Test
    void factorsARuleRelatesAreShownNothingOf() {
        String prelude = """
                data Pair = { a: Int, b: Int }
                    invariant a <= b
                """;
        Compilation compilation = compiled(prelude, "p: Pair", "p.a * p.b >= 1000");
        assertEquals(List.of("1000"), bordersOf(linesOf(compilation)));
        PartitionEvidence measured = measured(compilation);
        assertEquals(List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES,
                        UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                reasonsOf(measured));
        assertEquals(Map.of(), classesOf(measured), "neither factor is divided");
    }

    /**
     * A product an invariant states is one the reading of its ends does not read, and that
     * reading tells each factor so. A line drawn on the product beside that would say of one
     * comparison that it was read and that it was not, so the invariant draws none and stays a rule
     * nothing read — weighed after the product or not. The same rule in a body is read, draws its
     * line, and makes nought a class of each factor.
     */
    @Test
    void anInvariantOverAProductDrawsNoLineAndStaysUnread() {
        for (String rule : List.of("rate * cap >= 10", "rate * cap * 2 >= 10")) {
            String declared = """
                    data Policy = { rate: Int, cap: Int }
                        invariant %s
                    """.formatted(rule);
            Compilation compilation = compiled(declared, "p: Policy", List.of("Ok"), "");
            assertEquals(List.of(), bordersOf(linesOf(compilation)), rule);
            PartitionEvidence measured = measured(compilation);
            assertTrue(reasonsOf(measured).contains(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    rule + ": " + reasonsOf(measured));
            Map<String, List<String>> classes = classesOf(measured);
            assertTrue(!classes.containsKey("p.rate") && !classes.containsKey("p.cap"),
                    rule + ": " + classes);
        }

        String plain = "data Policy = { rate: Int, cap: Int }";
        Compilation guard = compiled(plain, "p: Policy", "p.rate * p.cap >= 10");
        assertEquals(List.of("10"), bordersOf(linesOf(guard)));
        Map<String, List<String>> guarded = classesOf(measured(guard));
        assertEquals(List.of("p.rate/= 0", "p.rate//= 0"), guarded.get("p.rate"),
                guarded.toString());
    }

    /**
     * Whether a clause draws a line is asked of that clause: the end {@code rate >= 0} places
     * beside an unread product is still drawn, and a sum and a length an invariant relates to a
     * field, which the reading of ends reads, still draw theirs. So do the days between two dates
     * and a comparison of two decimals, which the reading of ends has no atom for and names no
     * operation of: what it tells their places says nothing a line contradicts.
     */
    @Test
    void anUnreadClauseTakesNoOtherClausesLineWithIt() {
        Compilation beside = compiled("""
                data Policy = { rate: Int, cap: Int }
                    invariant rate >= 0 && rate * cap >= 10
                """, "p: Policy", List.of("Ok"), "");
        List<BorderAssessment> lines = linesOf(beside);
        assertEquals(List.of(), bordersOf(lines));
        assertTrue(lines.stream().anyMatch(each -> each.axis().equals("f/p.rate")
                && each.value().equals("0")), describe(lines));

        for (String[] related : List.of(new String[] {"a: Int, b: Int", "a + b >= 1000", "+"},
                new String[] {"a: Int, s: String", "String.length(s) <= a", "length"},
                new String[] {"from: Date, to: Date", "Date.daysBetween(from, to) >= 3", "from"},
                new String[] {"a: Decimal, b: Decimal", "Decimal.compare(a, b) <= 0", "p.a"})) {
            List<BorderAssessment> drawn = linesOf(compiled("""
                    data Pair = { %s }
                        invariant %s
                    """.formatted(related[0], related[1]), "p: Pair", List.of("Ok"), ""));
            assertTrue(drawn.stream().anyMatch(each -> each.axis().contains(related[2])),
                    related[1] + ": " + describe(drawn));
        }
    }

    private static String describe(List<BorderAssessment> lines) {
        return lines.stream().map(each -> each.axis() + " @ " + each.value()).toList().toString();
    }

    /**
     * An end of the type the relation comes out one way at only because the partner would pass
     * where the type stops is no class, for a product as for an order. A factor held to the least
     * {@code Int} and the one above it fails {@code a * b >= 1000} at the least whatever {@code b}
     * the run can multiply it by, and draws no line there, as a value held to the greatest
     * {@code Int} and the one below it fails {@code x < y} at the greatest and draws none.
     */
    @Test
    void anEndOfTheTypeIsNoClassOfAProductAsOfAnOrder() {
        Map<String, List<String>> product = classesOf(measured(compiled("""
                data Low = Int
                    invariant value <= -9223372036854775807
                """, "a: Low, b: Int", "a.value * b >= 1000")));
        assertTrue(!product.containsKey("a"), product.toString());

        Map<String, List<String>> order = classesOf(measured(compiled("""
                data High = Int
                    invariant value >= 9223372036854775806
                """, "x: High, y: Int", "x.value < y")));
        assertTrue(!order.containsKey("x"), order.toString());
    }

    /**
     * A row whose product passes where the type stops has no product, which is not the exact
     * arithmetic failing to hold one: the run stops there, and the row stands on neither side of a
     * line on the product. The least value times one and the greatest times one are products; the
     * least times minus one and the greatest times two are not.
     */
    @Test
    void aProductPastWhereTheTypeStopsIsNone() {
        NumericTerm x = new NumericTerm.ValueOf(TermPath.of("x"));
        NumericTerm y = new NumericTerm.ValueOf(TermPath.of("y"));
        long least = Long.MIN_VALUE;
        long greatest = Long.MAX_VALUE;
        assertEquals(Optional.empty(), productOf(x, y, least, -1));
        assertEquals(Optional.empty(), productOf(x, y, greatest, 2));
        assertEquals(Optional.of(ExactRatio.of(least)), productOf(x, y, least, 1));
        assertEquals(Optional.of(ExactRatio.of(greatest)), productOf(x, y, greatest, 1));
        assertEquals(Optional.of(ExactRatio.ZERO), productOf(x, y, least, 0));
    }

    private static Optional<ExactRatio> productOf(NumericTerm x, NumericTerm y, long one,
                                                  long other) {
        Map<NumericTerm, Place> values = new LinkedHashMap<>();
        values.put(x, Count.of(one));
        values.put(y, Count.of(other));
        return OrderedAffineBoundary.productAt(List.of(x, y), values)
                instanceof ExactAnswer.Held<Optional<ExactRatio>>(var product) ? product : null;
    }

    /** One row of a measurement: what each input was written as and what each point is for. */
    private record Row(List<String> inputs, List<String> labels) {}

    private static List<Row> certifiedRows(List<BorderAssessment> lines) {
        List<Row> rows = new ArrayList<>();
        for (BorderAssessment border : lines) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                        List<String> labels = new ArrayList<>();
                        certified.row().purposes().forEach(each -> labels.addAll(each.labels()));
                        rows.add(new Row(certified.row().inputs().stream()
                                .map(each -> each.text()).toList(), labels));
                    }
                }
            }
        }
        return rows;
    }

    /** The points of {@code line} a row is owed at and none was built for, by name. */
    private static List<String> pointsWithNoRow(BorderAssessment line) {
        List<String> out = new ArrayList<>();
        line.items().forEach((point, item) -> {
            if (item instanceof ItemAssessment.Owed owed && owed.searches().each().stream()
                    .noneMatch(ItemAssessment.Attempt.Certified.class::isInstance)) {
                out.add(point + " of " + line.axis() + " @ " + line.value());
            }
        });
        return out;
    }

    private static List<BorderAssessment> linesOf(Compilation compilation) {
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "demo");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }

    /** The values the lines of the product are drawn at, leaving out the lines on one factor. */
    private static List<String> bordersOf(List<BorderAssessment> lines) {
        return lines.stream().filter(each -> each.axis().contains(" * "))
                .map(BorderAssessment::value).toList();
    }

    private static PartitionEvidence measured(Compilation compilation) {
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get("f");
        assertNotNull(evidence, "f was measured");
        return evidence;
    }

    /** The classes of each axis, by the path of the position it divides. */
    private static Map<String, List<String>> classesOf(PartitionEvidence evidence) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        evidence.axes().forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    /** The reasons that say a rule was not read: those beside the ones that say it was read and
     *  divides no position. */
    private static List<UndividedPosition.Reason> unreadReasonsOf(PartitionEvidence evidence) {
        return reasonsOf(evidence).stream()
                .filter(reason -> reason != UndividedPosition.Reason.RULE_RELATING_TWO_VALUES
                        && reason != UndividedPosition.Reason.RULE_ABOUT_A_RUN
                        && reason != UndividedPosition.Reason.RULE_NEVER_TURNS_ON_THIS_LINE)
                .toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(PartitionEvidence evidence) {
        return evidence.notRead().stream().map(PartitionEvidence.NotRead::reason).distinct()
                .toList();
    }

    private static Compilation compiled(String prelude, String parameters, String condition) {
        return compiled(prelude, parameters, List.of("guard " + condition + " else No", "Ok"), "");
    }

    /** {@code f} over {@code parameters}, its body the lines given, after the declarations
     *  {@code prelude} writes and with the examples after it. */
    private static Compilation compiled(String prelude, String parameters, List<String> body,
                                        String examples) {
        String model = """
                module demo

                data Ok
                data No

                %s

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    %s
                }
                %s
                """.formatted(prelude, parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), String.join("\n    ", body),
                examples);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
