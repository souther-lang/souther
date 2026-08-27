package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.UnreadReason;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A question stands with every reason it stands for, and not with the first of them.
 *
 * <p>One clause names one position in as many parts as its author wrote about it, and two of those
 * parts stop the reading of values in two ways: a relation between two positions is a rule this
 * reading recognised and has no set of one position's values for, and a pattern is a form it does
 * not take apart at all. The two are lifted by different work and a report writes a different word
 * for each.
 *
 * <p>Held as one reason, which of them an author was shown turned on the order the parts were met
 * in, and the other was gone with nothing saying so. So this asks for both, and asks for them in
 * the order the clause writes them: an answer that came out as a set would be the same assertion
 * with the order left to whatever a hash happened to do.
 */
class EveryPartAReadingStoppedOnSaysWhyTest {

    /** A relation and a pattern about one position, in one clause. */
    private static final String TWO_PARTS_AT_ONE_POSITION = """
            module demo

            data N = { a: String, b: String }
                invariant both = a /= b && String.matches("x+", a)
            """;

    /** The two written the other way round, which is the same clause. */
    private static final String THE_OTHER_ORDER = """
            module demo

            data N = { a: String, b: String }
                invariant both = String.matches("x+", a) && a /= b
            """;

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /** What the reading of values was stopped by, over every question of every rule of the value. */
    private static List<UnreadReason> stoppedBy(FieldDomains read) {
        return read.accounting().values().stream()
                .flatMap(each -> each.answers().values().stream())
                .filter(RuleAccounting.Outcome.Unaccounted.class::isInstance)
                .map(each -> ((RuleAccounting.Outcome.Unaccounted) each).why())
                .filter(RuleAccounting.Why.TheValueReadingSays.class::isInstance)
                .flatMap(each -> ((RuleAccounting.Why.TheValueReadingSays) each).why().stream())
                .toList();
    }

    /** Both parts say why, and neither stands in for the other. */
    @Test
    void aQuestionStandsWithEveryReasonItStandsFor() {
        assertEquals(
                List.of(UnreadReason.RELATES_TWO_POSITIONS, UnreadReason.FORM_NOT_READ),
                stoppedBy(read(TWO_PARTS_AT_ONE_POSITION)));
    }

    /**
     * And in the order the clause writes them.
     *
     * <p>The two assertions together are what says the reasons are not a set. Asked of one order
     * only, a reading that sorted them or held them in a hash would pass — and an author reading
     * their own rules back would meet them in an order nothing in their model decides.
     */
    @Test
    void andInTheOrderTheClauseWritesThem() {
        assertEquals(
                List.of(UnreadReason.FORM_NOT_READ, UnreadReason.RELATES_TWO_POSITIONS),
                stoppedBy(read(THE_OTHER_ORDER)));
    }
}
