package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AsACompilationAllows;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A container filled to a total holds, in every element, what the caller asked of the positions
 * inside them.
 *
 * <p>A total is a demand on the whole container and a value fixed at {@code ns[*].payer} is a
 * demand on a position inside it, and the two are one value asked for twice. What answers both is
 * an element planned against both at once: the case the caller named, the payer the caller fixed,
 * and the amount the split put there — so the container is one value and nothing is written beside
 * it.
 */
class AContainerAddingUpHoldsWhatItsElementsAreAskedForTest {

    private static final String MODEL = """
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

            data Self
            data Company
            data Payer = Self | Company

            data Entry = { method: Method, payer: Payer }

            data Page = { count: Int }

            behavior readArticles : (ns: List<Entry>) -> Page
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ELEMENT = TermPath.of("ns").element();

    /**
     * Every container holds the case and the payer that were asked for, with the amounts coming to
     * the total.
     */
    @Test
    void everyElementHoldsTheCaseAndTheValueAskedFor() {
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        DemandsInside inside = new DemandsInside(
                Map.of(ELEMENT.then("payer"), company(rules.symbols())),
                Requirements.NONE.and(ELEMENT.then("method"), toLeaf("Cash")));

        assertEquals(List.of(
                        "[" + cash(1) + "]",
                        "[" + cash(1) + ", " + cash(0) + "]",
                        "[" + cash(0) + ", " + cash(1) + "]",
                        "[" + cash(1) + ", " + cash(0) + ", " + cash(0) + "]"),
                assertInstanceOf(TermRealizations.Realization.Built.class,
                        realizing(rules, inside),
                        "a list of cash entries paid by the company coming to one is a container"
                                + " this composes")
                        .values().stream().map(FixtureTemplate::text).toList(),
                "one container per count, every element in the case asked for and holding the"
                        + " payer asked for");
    }

    /**
     * And where what is asked inside cannot be one element, the container is one this composed
     * none of — said the way a total nothing composes is said, and never as two values written at
     * one place.
     */
    @Test
    void whatNoElementCanHoldIsAContainerNothingComposes() {
        RuleReadingSource rules = RuleReadings.ofSource(MODEL);
        // A value of the card's issuer fixed under an element the caller has said is cash.
        DemandsInside inside = new DemandsInside(
                Map.of(ELEMENT.then("method").refine(toLeaf("Card")).then("issuer"),
                        FixtureTemplate.string("x")),
                Requirements.NONE.and(ELEMENT.then("method"), toLeaf("Cash")));

        assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                assertInstanceOf(TermRealizations.Realization.None.class,
                        realizing(rules, inside),
                        "no element is both a card and cash").why());
    }

    /** What filling the entries to a total of one came to, with {@code inside} asked of each. */
    private static TermRealizations.Realization realizing(RuleReadingSource rules,
                                                          DemandsInside inside) {
        Symbols symbols = rules.symbols();
        NumericTerm.TakenOver total = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ProjectedOccurrences(ELEMENT.then("method").then("amount")),
                named("Amount"), ScopedDeclarations.wrapsOf(symbols), symbols);
        assertNotNull(total, "adding up the amounts of a run is a number of it");
        TermOrders orders = TermOrdersFixtures.at(total, named("Amount"), symbols);
        assertNotNull(orders.answered(), "and the order it answers on is the amounts'");

        return ContainersAddingUp.to(Count.of(1), new Type.ListOf(named("Entry")), orders,
                NothingTheRulesSay.REGION, RuleReadingContext.unshared(rules, POLICY), inside);
    }

    /** An entry of the case and payer asked for, holding {@code amount}. */
    private static String cash(int amount) {
        return "Entry { method = Cash { amount = Amount(" + amount + "), note = Note(\"x\") }"
                + ", payer = Company }";
    }

    /** The unit case {@code Company}, as the model writes it. */
    private static FixtureTemplate company(Symbols symbols) {
        return FixtureTemplate.unitCase(assertInstanceOf(TypeReachName.Written.class,
                symbols.scope().reach(declared("Company")), "the model can name its own case"));
    }

    /** The narrowing to one leaf of a sum. */
    private static Refinement toLeaf(String leaf) {
        return Refinement.of(ResolvedCase.of(CaseSelector.direct(declared(leaf)),
                List.of(declared(leaf))));
    }

    private static TypeSymbol declared(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }

    private static Type named(String data) {
        return Type.ref(declared(data));
    }
}
