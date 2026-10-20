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
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A remainder of a form beside a number the form does not name is realized at the remainder the
 * number leaves it, wherever the divisor puts that remainder.
 *
 * <p>The item is the remainder of {@code x} by 257 less {@code y}, at nought, with the rules
 * leaving {@code y} at a hundred. The remainder is then a hundred and nothing else, and the row is
 * an {@code x} that leaves a hundred. A search that tried the remainders from nought for a fixed
 * few would not reach it.
 */
class ARemainderBesideANumberIsRealizedAtTheRemainderTheNumberLeavesTest {

    private static final String PAIR = """
            module g

            data Ok

            behavior read : (x: Int, y: Int, z: Int) -> Ok
            """;

    private static final BigInteger DIVISOR = BigInteger.valueOf(257);

    private static final Read READ = read();

    @Test
    void theRemainderTheNumberLeavesIsTheOneTheRowIsAt() {
        SearchRegion yIsAHundred = READ.region().assuming(
                new LinearForm<>(ExactRatio.of(-100), Map.of(term("y"), ExactRatio.ONE)),
                Rel.EQ).taken();

        Realization made = new LevelRealizer().realize(remainderLessYAtNought(), yIsAHundred,
                NothingTheDeclarationsRefuse.at(path("x"), path("y"), path("z")));

        Realization.Found found = assertInstanceOf(Realization.Found.class, made);
        Place x = found.fixing().get(RealizationTarget.of(term("x")));
        Place y = found.fixing().get(RealizationTarget.of(term("y")));
        assertEquals(ExactRatio.of(100), Count.number(y).exactly());
        assertEquals(ExactAnswer.held(BigInteger.valueOf(100)),
                Count.number(x).exactly().floor().map(whole -> whole.mod(DIVISOR)));
    }

    /**
     * An arrangement a row was built from that did not stand is not offered again, whichever part
     * of the item it is the other part's that is asked for: the dividend is {@code x + y}, held to
     * a hundred and so to a remainder of a hundred, and the second asking is handed the whole of
     * the first arrangement and is answered with a different split of the dividend.
     */
    @Test
    void anArrangementTriedBeforeIsNotOfferedAgainForTheDividend() {
        SearchRegion held = READ.region()
                .assuming(new LinearForm<>(ExactRatio.of(-100), Map.of(term("x"), ExactRatio.ONE,
                        term("y"), ExactRatio.ONE)), Rel.EQ).taken()
                .assuming(new LinearForm<>(ExactRatio.of(-100),
                        Map.of(term("z"), ExactRatio.ONE)), Rel.EQ).taken();
        Standing standing = dividendIsXPlusYAndZIsAdded();
        WitnessSearch looking = NothingTheDeclarationsRefuse.at(path("x"), path("y"), path("z"));

        Realization first = new LevelRealizer().realize(standing, held, looking);
        Realization.Found built = assertInstanceOf(Realization.Found.class, first);

        Realization again = new LevelRealizer().realize(standing, held, looking,
                new ValuesTried(List.of(built.fixing())));

        Realization.Found other = assertInstanceOf(Realization.Found.class, again);
        assertNotEquals(sameOnes(built), sameOnes(other),
                "the arrangement that did not stand is not handed back");
    }

    /** What an arrangement puts at each of its targets, to compare two of them. */
    private static Map<String, ExactRatio> sameOnes(Realization.Found found) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        found.fixing().forEach((target, place) ->
                out.put(target.toString(), Count.number(place).exactly()));
        return out;
    }

    /** {@code Int.floorMod(x + y, 257) - z}, at nought. */
    private static Standing dividendIsXPlusYAndZIsAdded() {
        Map<NumericTerm, ExactRatio> dividend = new LinkedHashMap<>();
        dividend.put(term("x"), ExactRatio.ONE);
        dividend.put(term("y"), ExactRatio.ONE);
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        on.put(term("x"), Carrier.WHOLE);
        on.put(term("y"), Carrier.WHOLE);
        return new Standing.OfARemainderAndAForm(new LinearForm<>(ExactRatio.ZERO, dividend), on,
                DIVISOR, new LinearForm<>(ExactRatio.ZERO,
                        Map.of(term("z"), ExactRatio.ONE.negated())),
                Map.of(term("z"), Carrier.WHOLE), LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(0)));
    }

    /** {@code Int.floorMod(x, 257) - y}, at nought. */
    private static Standing remainderLessYAtNought() {
        Map<NumericTerm, ExactRatio> negated = new LinkedHashMap<>();
        negated.put(term("y"), ExactRatio.ONE.negated());
        return new Standing.OfARemainderAndAForm(
                new LinearForm<>(ExactRatio.ZERO, Map.of(term("x"), ExactRatio.ONE)),
                Map.of(term("x"), Carrier.WHOLE), DIVISOR,
                new LinearForm<>(ExactRatio.ZERO, negated), Map.of(term("y"), Carrier.WHOLE),
                LevelSpace.steppingBy(ExactRatio.ONE),
                new Criterion.AtTheLevel(Level.OfTheQuantity.of(0)));
    }

    private static NumericTerm.FromOnePosition term(String spelled) {
        return new NumericTerm.ValueOf(path(spelled));
    }

    private static TermPath path(String spelled) {
        return READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow();
    }

    private record Read(InputDomain input, RuleReadingSource rules) {

        SearchRegion region() {
            return input.quantities(rules).region();
        }
    }

    private static Read read() {
        Compilation compilation =
                Compilation.ofSources(List.of(PAIR), souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        return new Read(InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none()), rules);
    }
}
