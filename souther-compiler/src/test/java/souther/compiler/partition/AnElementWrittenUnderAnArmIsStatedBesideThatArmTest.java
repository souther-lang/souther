package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * That some element of a list a closure wrote under one arm meets a statement is that the arm is
 * taken for a piece and the statement holds of the piece, together.
 */
class AnElementWrittenUnderAnArmIsStatedBesideThatArmTest {

    private static final String ATTEMPT = """
            List.length(List.flatMap(n -> List.filter(a -> a.name == n.value, rows),
                    List.flatMap(d -> if Letters(d) as n then [ n ] else [ ],
                                 String.split("@", s)))) >= 1""";

    private static List<Proposition> partsOfWhatSomeRowMeets(Proposition stated) {
        Proposition.Some some = assertInstanceOf(Proposition.Some.class, stated);
        assertEquals("rows", some.container().toString().replaceAll(".*?(rows).*", "$1"));
        return assertInstanceOf(Proposition.All.class, some.ofTheElement()).parts();
    }

    /**
     * Some row has the name of a piece the attempt builds a value of: the row's name is one of the
     * pieces, and it is in the language the attempt builds, both of the one row. Without the
     * language the statement would be about a piece the attempt does not build.
     */
    @Test
    void theArmBeingTakenIsStatedBesideTheRowBeingAPiece() {
        List<Proposition> parts = partsOfWhatSomeRowMeets(stated(ATTEMPT));
        assertEquals(2, parts.size(), parts::toString);
        assertInstanceOf(Proposition.Compared.class, parts.get(0));
        Proposition.InTheStrings language = assertInstanceOf(Proposition.InTheStrings.class,
                parts.get(1));
        assertEquals(true, language.holds());
        assertEquals(Proposition.InTheStrings.Strings.AtAPosition.class,
                language.of().getClass());
        assertEquals(true, language.accepts().toString().contains("0061-007A"),
                language::toString);
    }


    /** What the condition of the fork on {@code truth} states. */
    private static Proposition stated(String truth) {
        String source = """
                module p
                data Letters = String
                    invariant String.matches("[a-z]+", value)
                data Row = { name: String }
                data Yes
                data No
                behavior f : (s: String, rows: List<Row>) -> Yes | No
                    constructs Letters
                let f (s, rows) = if %s then Yes else No
                """.formatted(truth);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("p")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "p");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("p")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body is one fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty())
                .proposition();
    }
}
