package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Ast;
import souther.compiler.check.Resolve;
import souther.compiler.check.Symbols;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a type declares and what a position can hold are two facts, crossed once.
 *
 * <p>{@code data StageI = Stage invariant value >= Qualified} declares three cases and holds two of
 * them: {@code StageI(Prospecting)} is refused at construction by the rule that says so. A class for
 * it would be a row nobody can write, asked for by the same report that has the rule in front of it.
 *
 * <p>Both halves are asserted because the crossing is only worth anything if the two are apart. The
 * reading of the declaration does not consult a rule, and the rule does not decide what the
 * declaration says — so neither is the other's input, and no order of working them out changes the
 * answer. Written as one reading handing its output to the other, the case comes back the day
 * somebody tidies the order.
 */
class ADeclaredCaseIsNotYetAClassThePositionHoldsTest {

    private static final String MODEL = """
            module demo

            data Ok
            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won
            data StageI = Stage invariant value >= Qualified

            behavior boundStage : (x: StageI) -> Ok constructs Ok
            let boundStage (x) = Ok

            behavior guardStage : (x: Stage) -> Ok constructs Ok
            let guardStage (x) = { guard x < Qualified else Ok
                Ok }
            """;

    private final Symbols symbols = Symbols.of(resolved());

    private static Ast.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODEL);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    /** The declaration's own answer, which the rule on the newtype does not enter into. */
    @Test
    void theTypeDeclaresEveryCaseWhateverItsRulesSay() {
        assertEquals(List.of("Prospecting", "Qualified", "Won"),
                Partitions.classesOf(Type.ref(symbols.own("StageI")), symbols).stream()
                        .map(PartitionClass::id).toList());
    }

    /** And the position holds the ones its rules leave. */
    @Test
    void thePositionHoldsTheCasesItsRulesAdmit() {
        assertEquals(List.of("Qualified", "Won"), measured("boundStage"));
    }

    /** A {@code guard} takes no case away: it cuts the same order and everything either side of the
     *  cut is still a value the position holds. */
    @Test
    void aLineDrawnByABodyTakesNoCaseAway() {
        assertEquals(List.of("Prospecting", "Qualified", "Won"), measured("guardStage"));
    }

    private static List<String> measured(String behavior) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage("demo")).value().get(behavior);
        assertNotNull(evidence, behavior + " was measured");
        return evidence.axes().get(0).classes();
    }
}
