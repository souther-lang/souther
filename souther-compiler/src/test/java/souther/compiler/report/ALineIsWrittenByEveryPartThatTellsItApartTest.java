package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Carrier;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.RuleRef;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Towards;
import souther.compiler.partition.AuthoredLine;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.BoundaryLine;
import souther.compiler.partition.BoundaryTarget;
import souther.compiler.partition.Level;
import souther.compiler.partition.LineFacts;
import souther.compiler.partition.WhichLine;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A document writes two lines alike exactly when they are one line.
 *
 * <p>Which line a line is, is {@link BoundaryLine}'s answer, and a document that names a line names
 * it by what {@code boundaryLineId} writes for one. Both directions are asked. A part of the line
 * left out of what is written makes two lines one entry, and the canonical order of the entries
 * then refuses the document; anything written that the line is not equal by makes one line two.
 * The second cannot be reached through {@code boundaryLineId} at all, which takes the line and
 * nothing a reading of it carried, so what is asked here is the first: every part a line is equal
 * by is one the document writes.
 *
 * <p>Built rather than found. The models this repository carries draw few of the shapes below, and
 * a quotient by two beside a quotient by three, or a sum's case beside an optional under one word,
 * is a pair none of them has. Each line here differs from the first in one part, so a part the
 * writer left out is a pair this test names.
 */
class ALineIsWrittenByEveryPartThatTellsItApartTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());

    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);

    private static final ValueName.Stdlib QUOTIENT =
            ValueName.Stdlib.operation("Int", "truncatingDivide");

    /**
     * Every pair, both ways: equal lines are written alike, and unequal ones are not.
     *
     * <p>Two lists of the same lines made twice, so a line is compared with a value equal to it and
     * not with itself — an id that carried something made fresh per value would be told apart from
     * its own copy.
     */
    @Test
    void twoLinesAreWrittenAlikeExactlyWhenTheyAreOneLine() {
        List<BoundaryLine> lines = lines();
        List<BoundaryLine> again = lines();
        assertEquals(lines.size(), new LinkedHashSet<>(lines).size(),
                "each line here is one no other line here is equal to");
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < lines.size(); i++) {
            for (int j = 0; j < again.size(); j++) {
                BoundaryLine one = lines.get(i);
                BoundaryLine other = again.get(j);
                if (one.equals(other) != idOf(one).equals(idOf(other))) {
                    wrong.add(i + " and " + j + ": " + idOf(one) + " / " + idOf(other));
                }
            }
        }
        assertEquals(List.of(), wrong,
                "pairs of lines written alike where they are two lines, or apart where one");
    }

    /**
     * A sum's case and an optional's present value are written {@code @Some} alike in the path an
     * author reads, and are two places.
     *
     * <p>The pair the spelling a person is shown cannot tell apart, asked on its own so that the
     * reason two such lines are two entries is said where it is held.
     */
    @Test
    void twoPlacesSpelledAlikeAreTwoLines() {
        TermPath underTheCase = TermPath.of("x").refine(theCaseNamedSome());
        TermPath underThePresentValue = TermPath.of("x").refine(aPresentValue());
        assertEquals(underTheCase.toString(), underThePresentValue.toString(),
                "an author reads both as one path");

        assertNotEquals(idOf(at(valueAt(underTheCase), whole(0), drawn(0))),
                idOf(at(valueAt(underThePresentValue), whole(0), drawn(0))),
                "and they are two places, so the lines at them are two lines");
    }

    /**
     * One line whose level two readings spelled differently is one line, written one way.
     *
     * <p>The other direction, asked where it can be got wrong. A level keeps how its rule wrote it,
     * and {@code 0} and {@code 0.00} are one place; a line told apart by the spelling would be two
     * entries of a document under one id, and an id that wrote the spelling would be two ids for
     * one line.
     */
    @Test
    void twoSpellingsOfOneLevelAreOneLineWrittenOneWay() {
        NumericTerm.ValueOf cost = valueAt(TermPath.of("cost"));
        BorderQuantity quantity = new BorderQuantity.OfACoordinate("b", cost,
                TermOrdersFixtures.itself(cost, Carrier.DENSE));
        BoundaryLine unspelled = new BoundaryLine(BoundaryTarget.at(quantity,
                new Level.OnACarrier(Carrier.DENSE, Count.of(new BigDecimal("0")))), drawn(0));
        BoundaryLine spelled = new BoundaryLine(BoundaryTarget.at(quantity,
                new Level.OnACarrier(Carrier.DENSE, Count.of(new BigDecimal("0.00")))), drawn(0));

        assertEquals(unspelled, spelled, "one line");
        assertEquals(idOf(unspelled), idOf(spelled), "written one way");
    }

    /**
     * One line, and lines each differing from it, or from another line here, in one component of
     * what a line is equal by.
     *
     * <p>Laid out by those components rather than by the shapes a model happens to draw, so a part
     * the writer leaves out is a pair named here. Each group says which equality it is walking:
     * the line's, the target's, the quantity's, a term's, the orders', a level's.
     */
    private static List<BoundaryLine> lines() {
        NumericTerm.ValueOf cost = valueAt(TermPath.of("cost"));
        NumericTerm.ValueOf fee = valueAt(TermPath.of("fee"));
        NumericTerm.TakenOf lengthOfName = lengthOf(TermPath.of("name"));
        NumericTerm.TakenOf lengthOfTitle = lengthOf(TermPath.of("title"));
        NumericTerm.TakenOf countOfLines = takenOfAList("length");
        NumericTerm.TakenOf sumOfLines = takenOfAList("sum");
        NumericTerm.TakenOf halved = quotientOf(TermPath.of("cost"), 2);
        NumericTerm.TakenOf thirded = quotientOf(TermPath.of("cost"), 3);
        NumericTerm.TakenOver totalOfLines = totalOver("lines");
        NumericTerm.TakenOver totalOfFees = totalOver("fees");
        Carrier stages = new Carrier.Ordinal(declared("Stage"),
                List.of(declared("Open"), declared("Shut")));
        Carrier stagesTheOtherWay = new Carrier.Ordinal(declared("Stage"),
                List.of(declared("Shut"), declared("Open")));
        return List.of(
                at(cost, whole(0), drawn(0)),
                // The line: which line of the model was drawn there.
                at(cost, whole(0), drawn(1)),
                // The target: which behavior's input the quantity is on.
                coordinate("other", cost, TermOrdersFixtures.itself(cost, Carrier.WHOLE),
                        whole(0)),
                // The target: where on the quantity it was cut, and what kind of level that is.
                at(cost, whole(1), drawn(0)),
                coordinate("b", cost, TermOrdersFixtures.itself(cost, Carrier.WHOLE), count(0)),
                // The quantity: its shape, where the terms it weighs and how are the same.
                new BoundaryLine(BoundaryTarget.at(new BorderQuantity.OverAForm("b",
                        LinearForm.<NumericTerm>atom(cost), Map.<NumericTerm, TermOrders>of(cost,
                                TermOrdersFixtures.itself(cost, Carrier.WHOLE))), whole(0)),
                        drawn(0)),
                // The quantity: which terms, which way and by how much.
                at(fee, whole(0), drawn(0)),
                new BoundaryLine(BoundaryTarget.at(apart(cost, fee), count(0)), drawn(0)),
                new BoundaryLine(BoundaryTarget.at(apart(fee, cost), count(0)), drawn(0)),
                new BoundaryLine(BoundaryTarget.at(form(cost, 2, fee, 1), count(9)), drawn(0)),
                new BoundaryLine(BoundaryTarget.at(form(cost, 3, fee, 1), count(9)), drawn(0)),
                new BoundaryLine(BoundaryTarget.at(form(cost, 2, fee, 3), count(9)), drawn(0)),
                // The orders a term stands on: what it is read on, and what it is measured on.
                coordinate("b", cost, TermOrdersFixtures.orders(cost, Carrier.DENSE, Carrier.WHOLE),
                        whole(0)),
                coordinate("b", cost, TermOrdersFixtures.orders(cost, Carrier.WHOLE, Carrier.DENSE),
                        whole(0)),
                // A level: the carrier it is on, the order that carrier is when it is a sum's cases.
                coordinate("b", cost, TermOrdersFixtures.itself(cost, Carrier.DENSE),
                        new Level.OnACarrier(Carrier.DENSE, Count.of(0))),
                coordinate("b", cost, TermOrdersFixtures.itself(cost, stages),
                        new Level.OnACarrier(stages, Count.of(0))),
                coordinate("b", cost, TermOrdersFixtures.itself(cost, stagesTheOtherWay),
                        new Level.OnACarrier(stagesTheOtherWay, Count.of(0))),
                // A number taken of a place: by which operation, of which place, given what.
                at(lengthOfName, whole(0), drawn(0)),
                at(lengthOfTitle, whole(0), drawn(0)),
                at(countOfLines, whole(0), drawn(0)),
                at(sumOfLines, whole(0), drawn(0)),
                at(halved, whole(0), drawn(0)),
                at(thirded, whole(0), drawn(0)),
                // A number taken over a run: of which values.
                new BoundaryLine(BoundaryTarget.at(form(totalOfLines, 2, fee, 1), count(9)),
                        drawn(0)),
                new BoundaryLine(BoundaryTarget.at(form(totalOfFees, 2, fee, 1), count(9)),
                        drawn(0)));
    }

    private static BoundaryLine coordinate(String behavior, NumericTerm.FromOnePosition term,
                                           TermOrders orders, Level level) {
        return new BoundaryLine(BoundaryTarget.at(
                new BorderQuantity.OfACoordinate(behavior, term, orders), level), drawn(0));
    }

    private static NumericTerm.TakenOf lengthOf(TermPath path) {
        return NumericTerm.TakenOf.of(ValueName.Stdlib.operation("String", "length"), path,
                Type.STRING, INNERS, SYMBOLS);
    }

    /** {@code List.<operation>} of the list at {@code lines}, which a count and a sum both take. */
    private static NumericTerm.TakenOf takenOfAList(String operation) {
        return NumericTerm.TakenOf.of(ValueName.Stdlib.operation("List", operation),
                TermPath.of("lines"), new Type.ListOf(Type.INT), INNERS, SYMBOLS);
    }

    /** The sum of every amount standing under {@code list}. */
    private static NumericTerm.TakenOver totalOver(String list) {
        return NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"),
                RunSource.overTheOccurrencesAt(TermPath.of(list).element().then("amount")),
                Type.INT, INNERS, SYMBOLS);
    }

    private static TypeSymbol declared(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }

    private static String idOf(BoundaryLine line) {
        ObjectNode into = JSON.createObjectNode();
        AdequacyReport.boundaryLineId(into, line);
        return into.toString();
    }

    private static BoundaryLine at(NumericTerm.FromOnePosition term, Level level,
                                   AuthoredLine line) {
        return new BoundaryLine(BoundaryTarget.at(new BorderQuantity.OfACoordinate("b", term,
                TermOrdersFixtures.itself(term, Carrier.WHOLE)), level), line);
    }

    private static BorderQuantity apart(NumericTerm.ValueOf on, NumericTerm.ValueOf against) {
        return new BorderQuantity.Apart("b", TermOrdersFixtures.itself(on, Carrier.WHOLE),
                TermOrdersFixtures.itself(against, Carrier.WHOLE));
    }

    private static BorderQuantity form(NumericTerm a, long weighed, NumericTerm b, long by) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(a, ExactRatio.of(weighed));
        coefs.put(b, ExactRatio.of(by));
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(a, TermOrdersFixtures.itself(a, Carrier.WHOLE));
        on.put(b, TermOrdersFixtures.itself(b, Carrier.WHOLE));
        return new BorderQuantity.OverAForm("b", new LinearForm<>(ExactRatio.ZERO, coefs), on);
    }

    private static NumericTerm.ValueOf valueAt(TermPath path) {
        return new NumericTerm.ValueOf(path);
    }

    private static NumericTerm.TakenOf quotientOf(TermPath path, long divisor) {
        return NumericTerm.TakenOf.of(QUOTIENT, path,
                TakenArguments.at(1, BigDecimal.valueOf(divisor)), Type.INT, INNERS, SYMBOLS);
    }

    private static Level whole(long at) {
        return new Level.OnACarrier(Carrier.WHOLE, Count.of(at));
    }

    private static Level count(long at) {
        return new Level.OfTheQuantity(ExactRatio.of(at));
    }

    /** A comparison written in a body, the {@code construct}th of it. */
    private static AuthoredLine drawn(int construct) {
        return new AuthoredLine(new WhichLine.OfAComparison(new RuleRef.Comparison("b",
                new SourceConstructOrigin(new WrittenOwner.Body("m", "b"), construct, 0,
                        SourceConstruct.BINARY))),
                new LineFacts(new ComparisonClaim.Cut(Towards.BELOW, true)), List.of());
    }

    private static Refinement theCaseNamedSome() {
        TypeSymbol some = TypeSymbols.declared(new TypeKey("m", "Some"));
        return Refinement.allOf(ResolvedCase.of(CaseSelector.direct(some), List.of(some)))
                .getFirst();
    }

    private static Refinement aPresentValue() {
        return Refinement.allOf(ResolvedCase.of(CaseSelector.optionPresent(Type.INT),
                List.of(TypeSymbol.SOME))).getFirst();
    }
}
