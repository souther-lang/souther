package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of what an operation answering the order of its two arguments answered states what
 * the same comparison written between the two arguments states.
 *
 * <p>Each condition is read beside the one an author would write without the operation, and the
 * two are held to one proposition: which argument is the greater, the relation and its denial, the
 * sign written on either side and against a number other than nought, the sign given a name first,
 * and an argument written out.
 */
class ASignOfAnOrderIsReadAsTheOrderOfItsArgumentsTest {

    private static final String INPUT = """
            data P = { x: Decimal, y: Decimal, n: Int, m: Int, d: Date, e: Date }
            """;

    private record Same(String written, String asTheOrder) {}

    private static final List<Same> CONDITIONS = List.of(
            new Same("Decimal.compare(p.x, p.y) > 0", "p.x > p.y"),
            new Same("Decimal.compare(p.y, p.x) > 0", "p.y > p.x"),
            new Same("Decimal.compare(p.x, p.y) < 0", "p.x < p.y"),
            new Same("Decimal.compare(p.x, p.y) <= 0", "p.x <= p.y"),
            new Same("Decimal.compare(p.x, p.y) >= 0", "p.x >= p.y"),
            new Same("Decimal.compare(p.x, p.y) == 0", "p.x == p.y"),
            new Same("Decimal.compare(p.x, p.y) /= 0", "p.x /= p.y"),
            new Same("0 < Decimal.compare(p.x, p.y)", "p.x > p.y"),
            new Same("0 >= Decimal.compare(p.x, p.y)", "p.x <= p.y"),
            new Same("Decimal.compare(p.x, p.y) >= 1", "p.x > p.y"),
            new Same("Decimal.compare(p.x, p.y) > -1", "p.x >= p.y"),
            new Same("Decimal.compare(p.x, p.y) == -1", "p.x < p.y"),
            new Same("Decimal.compare(p.x, 0.5m) < 0", "p.x < 0.5m"),
            new Same("Int.compare(p.n, p.m) <= 0", "p.n <= p.m"),
            new Same("Int.compare(p.n + 1, p.m) > 0", "p.n + 1 > p.m"));

    @Test
    void aComparisonOfTheSignStatesWhatTheComparisonOfTheArgumentsStates() {
        for (Same each : CONDITIONS) {
            Pullback.Pulled written = pulled("if %s then 1 else 0".formatted(each.written()));
            assertInstanceOf(Derivation.AnOrderOfItsArguments.class, written.meaning().how(),
                    () -> each.written() + " is read by the order its operation answers");
            assertEquals(pulled("if %s then 1 else 0".formatted(each.asTheOrder())).proposition(),
                    written.proposition(), () -> each.written() + " states " + each.asTheOrder());
        }
    }

    /** A name given the sign is the sign, and its arguments are read where they were written. */
    @Test
    void aSignGivenANameIsTheSign() {
        assertEquals(pulled("if p.x < p.y then 1 else 0").proposition(), pulled("""
                {
                        let sign = Decimal.compare(p.x, p.y)
                        if sign < 0 then 1 else 0
                    }""").proposition());
    }

    /** A comparison every answer the operation can give comes out the same against states no
     *  order. */
    @Test
    void aComparisonTheSignsBoundsSettleIsTheSameWhateverTheArguments() {
        Pullback.Pulled always = pulled("if Decimal.compare(p.x, p.y) > -2 then 1 else 0");
        assertInstanceOf(Derivation.ASignItsBoundsSettle.class, always.meaning().how());
        assertEquals(new Proposition.Always(true), always.proposition());
        assertEquals(new Proposition.Always(false),
                pulled("if Decimal.compare(p.x, p.y) > 1 then 1 else 0").proposition());
    }

    /**
     * A count of days held above one proves the later date is later and is not where it holds, so
     * no rule reads it as that order: what it states is a rule about the count.
     */
    @Test
    void aNumberThatOnlyProvesAnOrderIsNotReadAsIt() {
        assertTrue(byEachRule("Date.daysBetween(p.d, p.e) >= 0")
                        .contains(pulled("if p.e >= p.d then 1 else 0").proposition()),
                "a count held at or above nought is exactly the order, and is read as it");
        List<Proposition> byEach = byEachRule("Date.daysBetween(p.d, p.e) > 1");
        Proposition later = pulled("if p.e > p.d then 1 else 0").proposition();
        assertFalse(byEach.contains(later), () -> "no rule reads the count as the order it proves: "
                + byEach);
    }

    /** What each rule that takes {@code condition} reads it to, each on its own. */
    private static List<Proposition> byEachRule(String condition) {
        Fork fork = fork("if %s then 1 else 0".formatted(condition));
        StatedComparison comparison = BooleanMeaning.asAComparison(fork.condition())
                .orElseThrow(() -> new AssertionError(condition + " is a comparison"));
        return Pullback.byEachRule(comparison, fork.reads(), fork.read());
    }

    private record Fork(Core condition, InputReads reads, InputReading read) {}

    /** What the condition of the one fork of a body written {@code body} states. */
    private static Pullback.Pulled pulled(String body) {
        Fork fork = fork(body);
        return Pullback.ofATruth(fork.condition(), fork.reads(), fork.read(), Optional.empty());
    }

    /** The condition of the one fork of a body written {@code body}, as the reading meets it. */
    private static Fork fork(String body) {
        String model = "module demo\n\n" + INPUT + """

                behavior f : (p: P) -> Int
                let f (p) =
                    %s
                """.formatted(body);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), () -> "the model compiles: " + body);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model under test compiles");
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()));
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, () -> "the body is the fork: " + body);
        return new Fork(fork.cond(), reads, inputs.reading(rules));
    }
}
