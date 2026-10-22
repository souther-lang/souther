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
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A count of elements and the numbers added to it, asked again after the row built from the
 * arrangement the first asking offered did not stand, is offered a different split of the numbers
 * where the count can only be what it was.
 *
 * <p>The rules here keep {@code a} and {@code b} from nought and their sum from below one, so a
 * count above nought would need the numbers to sum to nought and the container holds none. At the
 * level of one the numbers are then {@code a = 0, b = 1} or {@code a = 1, b = 0}, and the first
 * split being tried must leave the search the other.
 */
class AnArrangementOfACountAndANumberTriedBeforeIsNotOfferedAgainTest {

    private static final String MODEL = """
            module g

            data Ok

            behavior counted : (xs: List<Int>, a: Int, b: Int) -> Ok
            """;

    @Test
    void anotherSplitOfTheNumbersIsOfferedForTheSameCount() {
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
        NumericTerm a = new NumericTerm.ValueOf(pathIn(input, "a"));
        NumericTerm b = new NumericTerm.ValueOf(pathIn(input, "b"));
        NumericTerm element = new NumericTerm.ValueOf(xs.element());
        SearchRegion region = measuring.region()
                .assuming(new LinearForm<>(ExactRatio.ZERO, Map.of(a, ExactRatio.ONE)),
                        Rel.GE).taken()
                .assuming(new LinearForm<>(ExactRatio.ZERO, Map.of(b, ExactRatio.ONE)),
                        Rel.GE).taken()
                .assuming(new LinearForm<>(ExactRatio.ONE.negated(),
                        Map.of(a, ExactRatio.ONE, b, ExactRatio.ONE)), Rel.GE).taken();

        Map<Quantity, ExactRatio> atLeast = new LinkedHashMap<>();
        atLeast.put(new DecisionAtom.OfTheInput(a), ExactRatio.ONE);
        atLeast.put(new DecisionAtom.OfTheInput(element), ExactRatio.ONE.negated());
        CountedElements counted = CountedElements.of("counted", new Quantity.HowManyMeet(
                new DecisionSubject.AnInput(xs),
                new Proposition.Compared(new Relation.Affine(
                        new LinearForm<>(ExactRatio.ZERO, atLeast), Rel.GE), false)), measuring,
                AnElementMeeting.UNREAD);
        Map<NumericTerm, ExactRatio> both = new LinkedHashMap<>();
        both.put(a, ExactRatio.ONE);
        both.put(b, ExactRatio.ONE);
        Standing standing = new Standing.OfACountAndAForm(counted,
                new LinearForm<>(ExactRatio.ZERO, both),
                Map.of(a, Carrier.WHOLE, b, Carrier.WHOLE),
                LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(1)));
        WitnessSearch looking = NothingTheDeclarationsRefuse.at(xs, pathIn(input, "a"),
                pathIn(input, "b"));

        Realization.Found built = assertInstanceOf(Realization.Found.class,
                new LevelRealizer().realize(standing, region, looking));
        Realization.Found other = assertInstanceOf(Realization.Found.class,
                new LevelRealizer().realize(standing, region, looking,
                        new ValuesTried(List.of(built.fixing()))));

        assertNotEquals(built.fixing().toString(), other.fixing().toString());
    }

    private static TermPath pathIn(InputDomain input, String spelled) {
        return input.positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow();
    }
}
