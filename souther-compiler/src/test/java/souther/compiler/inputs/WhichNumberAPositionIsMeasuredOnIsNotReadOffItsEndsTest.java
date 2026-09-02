package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A position is measured on the number its rules are about, whether or not any of them placed an
 * end.
 *
 * <p>A {@code String} is the one carrier with two numbers — its own order, and how long it is — so
 * which of them a position is measured on is what the model wrote about. Read off the ends instead,
 * a rule that writes about the length and places no end was no vote at all, and the position came
 * back measured on the string's order: the length was not a number of the model, and nothing that
 * is true of a length could reach it.
 *
 * <p>Nothing here is about where the values stop or about what a border is owed. Which number this
 * is is settled before either.
 */
class WhichNumberAPositionIsMeasuredOnIsNotReadOffItsEndsTest {

    /** An ordering of the length, which places an end and has always been read as one. */
    @Test
    void aRuleOrderingTheLengthMeasuresThePositionOnIt() {
        assertLength("String.length(value) >= 1");
    }

    /** One that holds the length away from a value, which places none. */
    @Test
    void aRuleHoldingTheLengthAwayFromAValueMeasuresThePositionOnIt() {
        assertLength("String.length(value) /= 0");
    }

    /** And one that names a length, which states both ends at once and so places neither. */
    @Test
    void aRuleNamingALengthMeasuresThePositionOnIt() {
        assertLength("String.length(value) == 5");
    }

    /** A rule on the string's own order still measures the position there. */
    @Test
    void aRuleOnTheValuesOwnOrderMeasuresThePositionOnTheValue() {
        assertInstanceOf(NumericTerm.ValueOf.class, termOf("value >= \"m\""),
                "the model wrote about the order the string sits on");
    }

    private static void assertLength(String invariant) {
        NumericTerm term = termOf(invariant);
        NumericTerm.TakenOf taken = assertInstanceOf(NumericTerm.TakenOf.class, term,
                "the model wrote about the length of the string");
        assertEquals("String.length", taken.operation().toString(),
                "and the length is the number it is measured on");
    }

    private static NumericTerm termOf(String invariant) {
        String source = """
                module example.axis

                data Subject = String
                    invariant %s

                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """.formatted(invariant);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("take")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = InputDomain.of(spec, sigs.get("take"), symbols,
                ReadAs.THE_COMPILATION_DOES);
        return inputs.at(TermPath.of("n")).term();
    }
}
