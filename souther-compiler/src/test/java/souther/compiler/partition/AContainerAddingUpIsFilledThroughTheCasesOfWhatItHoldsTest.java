package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A container is filled to a total through the cases of what it holds.
 *
 * <p>Where every case of a sum spreads the same declaration, a field of it is read through the sum:
 * the total {@code List.sum(ns[*].method.amount)} names a position of the sum and no case of it,
 * which is what makes the rule readable and is not enough to write a value with. A value of that
 * position is a value of one of the cases, and which one is a fact about the value — so the walk
 * offers one shape per case rather than choosing.
 *
 * <p>The way down is the plan's. Walked from the declarations instead, a field of a plain record at
 * a time, the sum was a shape it had no answer for: every count and every spread came back with
 * nothing built, and the point the total was about was reported in the words of a figure this
 * compiler had stopped at.
 */
class AContainerAddingUpIsFilledThroughTheCasesOfWhatItHoldsTest {

    /**
     * Entries whose method is a sum of two cases, the amount spread through both.
     *
     * <p>Each case carries a field of its own, so that composing one is composing a record and not
     * merely naming a case — which is the shape a model writes and the one this could not fill.
     */
    private static final String SHARED = """
            module g

            data Amount = Int
                invariant value >= 0

            data Common = { amount: Amount }

            data Card = { ...Common, issuer: Issuer }
            data Cash = { ...Common, note: Note }

            data Issuer = String
                invariant String.length(value) >= 1

            data Note = String
                invariant String.length(value) >= 1

            data Method = Card | Cash

            data Entry = { method: Method }

            data Page = { count: Int }

            behavior readArticles : (ns: List<Entry>) -> Page
            """;

    private static final RuleReadingSource RULES = RuleReadings.ofSource(SHARED);

    private static final Symbols SYMBOLS = RULES.symbols();

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12);

    /** What the behavior takes: a list of entries, which is the container the total is over. */
    private static final Type ENTRIES = new Type.ListOf(named("Entry"));

    /**
     * A total two counts reach, so that both a container of one and a container of two are among
     * what is offered.
     */
    private static final Count SIX = Count.of(6);

    /**
     * Every case is offered, and each container is a whole value of it.
     *
     * <p>The texts and not a count of them. What a case brings with it is the rest of its own
     * record, and a walk that reached the amount without composing the case around it would offer
     * as many containers as this and none the decoder accepts.
     */
    @Test
    void aContainerIsOfferedForEachCaseOfWhatItHolds() {
        assertEquals(List.of(
                        "[Entry { method = Card { amount = Amount(6), issuer = Issuer(\"x\") } }]",
                        "[Entry { method = Cash { amount = Amount(6), note = Note(\"x\") } }]",
                        "[Entry { method = Card { amount = Amount(6), issuer = Issuer(\"x\") } }"
                                + ", Entry { method = Card { amount = Amount(0)"
                                + ", issuer = Issuer(\"x\") } }]",
                        "[Entry { method = Cash { amount = Amount(6), note = Note(\"x\") } }"
                                + ", Entry { method = Cash { amount = Amount(0)"
                                + ", note = Note(\"x\") } }]"),
                offered().stream().map(FixtureTemplate::text).toList(),
                "one container per case at each count, with the case's own field beside the"
                        + " amount");
    }

    /** The containers this offered. */
    private static List<FixtureTemplate> offered() {
        NumericTerm.TakenOver total = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(
                        TermPath.of("ns").element().then("method").then("amount")),
                named("Amount"), SYMBOLS);
        assertNotNull(total, "adding up the amounts of a run is a number of it");
        TermOrders orders = TermOrdersFixtures.at(total, named("Amount"), SYMBOLS);
        assertNotNull(orders.answered(), "and the order it answers on is the amounts'");

        TermRealizations.Realization made = TermRealizations.at(ENTRIES, orders, SIX,
                NothingTheRulesSay.REGION, RULES, POLICY);
        return assertInstanceOf(TermRealizations.Realization.Built.class, made,
                "a list of entries whose amounts come to six is a container this composes")
                .values();
    }

    private static Type named(String data) {
        return Type.ref(TypeSymbols.declared(new TypeKey("g", data)));
    }
}
