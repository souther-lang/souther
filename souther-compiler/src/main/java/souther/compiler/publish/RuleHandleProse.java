package souther.compiler.publish;

import souther.compiler.diag.SourceRendering;
import souther.compiler.source.SourceId;

import java.util.Locale;

/**
 * What a rule handle reads as in the report a person reads.
 *
 * <p>The same handle a document writes, because a reader meeting a rule in the report and a
 * consumer meeting it in the document are meeting one rule, and two spellings of one handle read as
 * two handles. What may differ is a word joining its parts, which is said in the reader's language
 * here and in the document's language there.
 *
 * <p>Apart from {@link RuleHandleSurface} rather than an arm of it. What a person is shown is held
 * to nothing in the schema, so it is not one of the fields a check counts — and a renderer that
 * handed back a string a document writer could put anywhere would leave that count a list of the
 * places somebody remembered. Which classes may name this is written down
 * ({@code WhoMaySayWhatARuleHandleReadsAs}).
 */
public final class RuleHandleProse {

    private RuleHandleProse() {
    }

    /** {@code handle} in a report about {@code sectionSource}, with the sources under the names
     *  {@code names} gives them and the words between its parts in {@code language}. */
    public static String said(PublishedRuleHandle handle, SourceRendering sources,
                              Locale language, SourceId sectionSource) {
        return RuleHandleSentence.said(handle, sources, sectionSource, language);
    }

    /** The same for a sentence with a handle in it, so that the words around one are put together
     *  the one way wherever they are read. */
    public static String said(PublishedSentence sentence, SourceRendering sources,
                              Locale language, SourceId sectionSource) {
        return RuleHandleSentence.of(sentence, sources, sectionSource, language);
    }
}
