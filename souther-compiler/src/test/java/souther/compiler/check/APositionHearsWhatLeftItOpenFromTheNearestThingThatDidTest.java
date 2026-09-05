package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.values.UnreadReason;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a position is told about why it is open, and which of two reasons it is told.
 *
 * <p>A choice that offered an alternative nothing could read leaves the positions the alternative
 * beside it promised open. That fact is decided over the clause as its author wrote it, where the
 * alternatives are what stands between the brackets, and reaches a position from there — the join
 * that widens it holds branches every conjunction beside the choice was distributed into, and could
 * say neither which positions the alternative reached nor whether it was an alternative at all.
 *
 * <p><b>The nearer reason is what a position is told.</b> A rule written about the position that
 * nothing could read is what an author would lift; that the choice above carried the same openness
 * outward is true as well and is the coarser of the two, and telling both would have a reader lift
 * the form and find the question still there. Which is a rule about the two kinds of evidence and
 * not about the order a walk met them in.
 *
 * <p>And a position the rules pin anyway hears nothing. Whether the openness survived is the
 * answer's to say: where the two ends meet at a position there was nothing for an unread
 * alternative to have been.
 */
class APositionHearsWhatLeftItOpenFromTheNearestThingThatDidTest {

    /** A choice whose unread alternative is the only thing that leaves the other position open. */
    private static final String THE_CHOICE_IS_ALL_THERE_IS_TO_SAY = """
            module demo

            data N = { x: String, y: String }
                invariant r = x == "A" && (y == "A" || UNREAD_X)
            """.replace("UNREAD_X", souther.compiler.ARuleNoReadingTakesIn.about("x"));

    /** And one where the position has a rule of its own that nothing could read. */
    private static final String THE_POSITION_HAS_A_NEARER_REASON = """
            module demo

            data N = { x: String }
                invariant r = x /= "Z" || UNREAD_X
            """.replace("UNREAD_X", souther.compiler.ARuleNoReadingTakesIn.about("x"));

    /** A position no alternative of the choice reaches, pinned by the conjunct beside it. */
    private static final String THE_CONJUNCT_BESIDE_THE_BRACKETS_PINS_IT = """
            module demo

            data N = { x: String, y: String }
                invariant r = (x == "A" || UNREAD_X) && y == "Q"
            """.replace("UNREAD_X", souther.compiler.ARuleNoReadingTakesIn.about("x"));

    /** And the position the choice did leave open, pinned by the conjunct beside the brackets. */
    private static final String THE_CONJUNCT_PINS_WHAT_THE_CHOICE_LEFT_OPEN = """
            module demo

            data N = { x: String }
                invariant r = (x == "A" || UNREAD_X) && x == "A"
            """.replace("UNREAD_X", souther.compiler.ARuleNoReadingTakesIn.about("x"));

    /** And two alternatives that cover the position between them, with a third nothing read. */
    private static final String THE_ALTERNATIVES_COVER_IT_BETWEEN_THEM = """
            module demo

            data N = { x: String, y: String }
                invariant r = (x == "A" || x /= "A") || UNREAD_Y
            """.replace("UNREAD_Y", souther.compiler.ARuleNoReadingTakesIn.about("y"));

    /** Where nothing else left the position open, the choice is what it is told about. */
    @Test
    void aPositionHearsAboutTheChoiceWhereNothingNearerLeftItOpen() {
        assertEquals(List.of(UnreadReason.ALTERNATIVE_NOT_READ),
                whyOpen(THE_CHOICE_IS_ALL_THERE_IS_TO_SAY, "y"),
                "the alternative beside the unread one promised `y`, and nothing about `y` itself"
                        + " went unread");
    }

    /** And where a rule about the position went unread, that is what it is told about. */
    @Test
    void aRuleAboutThePositionOutranksTheChoiceThatCarriedItOutward() {
        assertEquals(List.of(UnreadReason.FORM_NOT_READ),
                whyOpen(THE_POSITION_HAS_A_NEARER_REASON, "x"),
                "the form nothing reads is what an author would lift, and the choice above it"
                        + " carried that openness outward rather than adding to it");
    }

    /** A position neither alternative reaches hears nothing about the choice. */
    @Test
    void aPositionTheAlternativesNeverReachHearsNothing() {
        assertEquals(List.of(), whyOpen(THE_CONJUNCT_BESIDE_THE_BRACKETS_PINS_IT, "y"),
                "`y` is written beside the brackets, so nothing about it turns on which"
                        + " alternative anybody is in");
    }

    /**
     * And a position the rules pin anyway hears nothing, though the choice did leave it open.
     *
     * <p>The half the answer decides. The choice offered an alternative nothing could read and the
     * position it promised is open by it — and a rule stated beside the brackets holds the position
     * to one value whichever alternative anybody is in, so there is nothing left for the unread one
     * to have taken back.
     */
    @Test
    void aPositionTheRulesPinAnywayHearsNothing() {
        assertEquals(List.of(), whyOpen(THE_CONJUNCT_PINS_WHAT_THE_CHOICE_LEFT_OPEN, "x"),
                "the two ends meet at `x`, so nothing was left for an unread alternative to widen");
    }

    /** And a position the alternatives cover between them hears nothing either. */
    @Test
    void aPositionTheAlternativesCoverBetweenThemHearsNothing() {
        assertEquals(List.of(), whyOpen(THE_ALTERNATIVES_COVER_IT_BETWEEN_THEM, "x"),
                "the two alternatives that were read admit every value at `x`, so the choice does"
                        + " whatever the one beside them turned out to say");
    }

    /** What the position is told left it open, empty where it is told nothing. */
    private static List<UnreadReason> whyOpen(String source, String field) {
        return switch (read(source).admits(RuleKey.of(field)).completeness()) {
            case AdmissibleSet.Completeness.Complete _ -> List.of();
            case AdmissibleSet.Completeness.Wider it -> it.why().stream()
                    .filter(AdmissibleSet.Widening.RuleUnread.class::isInstance)
                    .map(each -> ((AdmissibleSet.Widening.RuleUnread) each).why())
                    .toList();
        };
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadings.of(compilation, "demo"),
                ReadAs.THE_COMPILATION_DOES);
    }
}
