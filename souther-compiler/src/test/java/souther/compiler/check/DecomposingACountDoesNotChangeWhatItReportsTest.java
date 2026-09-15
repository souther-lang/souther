package souther.compiler.check;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A count taken a component at a time reports what one count of the whole graph would have.
 *
 * <p>The one thing the whole-graph entry is kept for. A component is answered under the counts its
 * own declarations' rules turn on, and a count of the whole module under every declaration's, so the
 * two round a standing count differently wherever a rule somewhere else in the module asked about a
 * number this component's rules do not. What is held is that no reader can tell: which declarations
 * no value satisfies, which of them are at fault for it together, where that is reported and what
 * shows it are the same either way.
 *
 * <p>Of the report and not of every count, because the report is what a count is asked for. Holding
 * the counts equal would hold the two ways of taking them to the same precision, which is the thing
 * the decomposition is allowed to change.
 *
 * <p>The models are the places the two ways could part: a chain answered one declaration at a time,
 * a declaration written in terms of itself, a component risen through under a count some other
 * declaration's rule asked about, a lack reaching another lack through a declaration that has
 * values, and a component reaching out of the module it is declared in. That a count short of a
 * rule says so either way is held where a count is made short
 * ({@link ACountOfWhatATypeHoldsSaysWhetherItGotEveryRuleTest}).
 */
class DecomposingACountDoesNotChangeWhatItReportsTest {

    private static final String MODULE = "demo";

    /**
     * The two ways of counting {@code documents} report alike, and what they report is
     * {@code named}.
     *
     * <p>Both, because the first alone would hold of a model neither way says anything about. What
     * each model is about is written beside it, so a model that stopped saying it is a failure
     * rather than a pair of empty reports agreeing.
     */
    private static void reportsAlike(String what, List<List<String>> named,
                                     Map<String, String> documents) {
        Compilation c = Compilation.ofDocuments(
                new LinkedHashMap<>(documents), Set.of(), ModulePath.EMPTY);
        c.answerEverything();

        List<TypeSymbol.AtModule> declared = c.db().ask(new Front.DeclaredTypes(MODULE)).value();
        RuleReadingSource source = Shapes.ruleReading(c.db(), MODULE).value();
        ReadingPolicy policy = c.db().ask(new Front.Reading()).value();
        List<UninhabitableTypes.UninhabitableGroup> whole = UninhabitableTypes.withNoValueOfTheirOwn(
                declared,
                TypeCardinality.overTheWholeGraph(declared, source, policy, c.db().readings(),
                        TypeCardinality.Premises.read(source, policy, c.db().readings())));

        assertEquals(named,
                whole.stream().map(each -> each.members().stream().map(TypeSymbol::name).toList())
                        .toList(),
                () -> "the model is no longer about what it was written for: " + what);
        assertEquals(new UninhabitableTypes.WithNoValue.Counted(whole),
                c.db().ask(new Shapes.TypesWithNoValue(MODULE)).value(),
                () -> "the components came to something one count of the whole graph would not"
                        + " have, for " + what);
    }

    private static void reportsAlike(String what, List<List<String>> named, String source) {
        reportsAlike(what, named, Map.of("demo.sou", source));
    }

    @Test
    void aChainAnsweredOneDeclarationAtATime() {
        reportsAlike("a chain", List.of(), """
                module demo exposing ( Tail, Held, Holding )

                data Tail = Int
                    invariant value >= 1 && value <= 9
                data Held = { tail: Tail }
                data Holding = { held: Held }
                """);
    }

    @Test
    void aDeclarationWrittenInTermsOfItself() {
        reportsAlike("a declaration written in terms of itself", List.of(List.of("Node")), """
                module demo exposing ( Node, Fine )

                data Node = { next: Node, fine: Fine }
                data Fine = Int
                    invariant value >= 1 && value <= 9
                """);
    }

    @Test
    void aRisingUnderACountAnotherDeclarationsRuleAskedAbout() {
        reportsAlike("a rising under a count asked about elsewhere", List.of(List.of("Pair")), """
                module demo exposing ( One, Pair, Both, Wide )

                data One = Int
                    invariant only = value >= 1 && value <= 1
                data Pair = Set<One>
                    invariant two = Set.size(value) >= 2
                data Both = { left: Wide, right: One }
                data Wide = Int
                    invariant wide = value >= 1 && value <= 500
                """);
    }

    @Test
    void aLackReachingAnotherThroughADeclarationThatHasValues() {
        reportsAlike("a lack reaching another through a declaration that has values",
                List.of(List.of("Bad")), """
                module demo exposing ( Bad, MaybeBad, NeedTwo, Beside )

                data Bad = Int
                    invariant no = value >= 2 && value <= 1

                data MaybeBad = { x: Bad? }

                data NeedTwo = Set<MaybeBad>
                    invariant two = Set.size(value) >= 2

                data Beside = Int
                    invariant value >= 1 && value <= 4
                """);
    }

    @Test
    void aComponentReachingOutOfTheModuleItIsDeclaredIn() {
        Map<String, String> documents = new LinkedHashMap<>();
        documents.put("other.sou", """
                module other exposing ( One )

                data One = Int
                    invariant only = value >= 1 && value <= 1
                """);
        // The lack is this module's own and the count that shows it is the other module's: what
        // fills the set is declared there, and how many values it has is what the set is short of.
        documents.put("demo.sou", """
                module demo exposing ( NeedTwo, Beside )

                import other ( One )

                data NeedTwo = Set<One>
                    invariant two = Set.size(value) >= 2

                data Beside = { one: One }
                """);
        reportsAlike("a component reaching out of its module",
                List.of(List.of("NeedTwo")), documents);
    }
}
