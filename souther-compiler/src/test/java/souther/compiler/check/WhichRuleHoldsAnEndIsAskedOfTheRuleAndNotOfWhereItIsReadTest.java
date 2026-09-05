package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which declaration holds an end is answered by taking that declaration's rules away, and a rule a
 * spread brought in is that declaration's.
 *
 * <p>A reading is asked to leave a declaration's clauses out so that the end which moves says which
 * declaration was holding it. What is left out is a property of each rule — the declaration that
 * wrote it — and not of the value the reading happens to be opened at. The two are the same name
 * only where a declaration writes its own clauses and spreads nothing, which is most of a model and
 * was every fixture that asked this question.
 *
 * <p>So a rule a spread carries in is left in whatever the reading was told, every end it holds is
 * held by nobody the reading can name, and the answer falls back to naming every declaration that
 * wrote a relation about the coordinate.
 */
class WhichRuleHoldsAnEndIsAskedOfTheRuleAndNotOfWhereItIsReadTest {

    private static final String SOURCE = """
            module demo exposing ( Held, keep )

            data Common =
                { lo: Int
                , hi: Int
                }
                invariant based = lo >= 100
                invariant far = hi >= lo + 10

            data Held = { ...Common }
                invariant near = hi >= lo + 5

            behavior keep : (h: Held) -> Held

            let keep (h) = h
            """;

    private final RuleReadingSource rules = rules();

    private static RuleReadingSource rules() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        return RuleReadings.of(compilation, compilation.modules().get(0));
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey("demo", name));
    }

    private FieldDomains reading() {
        return FieldDomains.of(named("Held"), rules,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /**
     * Two declarations write a lower end on one coordinate and only one of them holds it.
     *
     * <p>{@code Common} puts {@code hi} ten above {@code lo} and {@code Held} puts it five above,
     * so ten above is where {@code hi} stops and {@code Common} is what put it there. Taking
     * {@code Held}'s own clause away moves nothing; taking {@code Common}'s does.
     *
     * <p>Which is only answerable if leaving a declaration's clauses out leaves out the ones it
     * wrote rather than the ones read where it was. Read the second way, taking {@code Common} away
     * takes nothing away — its rule arrives through {@code Held} — so neither candidate moves the
     * end on its own and both are named.
     */
    @Test
    void aSpreadRuleIsHeldByTheDeclarationThatWroteIt() {
        List<String> holding = AReadingOfAPosition
                .holding(reading().at(RuleKey.of("hi")), souther.compiler.numeric.EndSide.LOWER)
                .stream()
                .map(TypeSymbol::name)
                .toList();

        assertEquals(List.of("Common"), holding,
                "ten above is the end, and Common is what says ten above");
    }
}
