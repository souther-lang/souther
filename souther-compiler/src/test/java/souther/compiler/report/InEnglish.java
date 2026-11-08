package souther.compiler.report;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.Message;

import java.util.Locale;

/**
 * A page for a test that reads what the report says in English, which is the language its
 * sentences are asserted in.
 */
final class InEnglish {

    /** A page in English whose sources stand for themselves and have no text laid out. */
    static final Page PAGE = new Page(SourceRendering.namedByIdentity(SourceLayouts.NONE),
            Locale.ENGLISH);

    /** {@code message} as an English reader is told it. */
    static String said(Message message) {
        return PAGE.say(message);
    }

    /** A page in English over {@code rendering}. */
    static Page page(SourceRendering rendering) {
        return new Page(rendering, Locale.ENGLISH);
    }

    private InEnglish() {}
}
