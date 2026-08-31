package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.inputs.BlockReason;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a reading stopped, each place it was left at says what stopped it there.
 *
 * <p>A comparison the arithmetic could not take apart has no quantity to be about, so there is no
 * one subject for the places it names to share. One of them may be a position the rule states
 * something about the values of, and the next may be a position the walk met on its way through an
 * expression it did not read — and what is true of the first is no fact about the second.
 *
 * <p>Worked out once from whichever side named a position and handed to all of them, the answer for
 * one was printed at the other: a carrier no line is drawn on is a fact about the position that
 * carries it, and a position beside it in the same comparison need not carry the same thing.
 */
class AStoppedReadingSaysWhatStoppedItAtEachPlaceTest {

    /**
     * One comparison, two places, two answers.
     *
     * <p>{@code s} is a whole side of the comparison, so the rule states something about the values
     * standing there — and nothing draws a line on a case of a sum, which is what a reader of
     * {@code s} is owed. {@code v} is where the walk met a position inside the call on the other
     * side, read through to a {@code match} it does not take apart; the rule states nothing about
     * which case stands there, and what it does say is the part that went unread.
     *
     * <p>Answered from a side of the comparison, both came back as a carrier nothing draws a line
     * on — because the side that names a position is {@code s}, and {@code v} was handed the answer
     * about {@code s}.
     */
    private static final String ONE_SIDE_IS_A_POSITION_AND_ONE_IS_NOT = """
            module demo

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Near = { q: Qualified }
            data Far = { q: Qualified }
            data Side = Near | Far

            let pick (v: Side) : Qualified = match v with
                | Near as n -> n.q
                | Far as f -> f.q

            data N = { s: Qualified, v: Side }
                invariant said = s < pick(v)
            """;

    @Test
    void twoPlacesOfOneComparisonSayTwoThings() {
        FieldDomains read = read(ONE_SIDE_IS_A_POSITION_AND_ONE_IS_NOT);

        assertEquals(List.of(new BlockReason.UnreadComparisonDomain()), reasonsAt(read, "s"),
                "a whole side is this position, so what its values are carried on is the answer");
        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "v"),
                "and here the walk met a position inside a form it did not read, which says "
                        + "nothing about what that position carries");
    }

    private static List<BlockReason.RuleWithoutLineReason> reasonsAt(FieldDomains read,
                                                                     String field) {
        return read.noLineAt(RuleKey.of(field)).stream().map(FieldDomains.NoLine::why).toList();
    }

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
}
