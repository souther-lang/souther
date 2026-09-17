package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What comes back from a format is the whole of what went in, or nothing comes back at all.
 *
 * <p>A formatter is a source-to-source transformation, so a caller that gets a String has to be
 * able to write it where the old one was. A recovering parse does not hold everything that was
 * written — a construct the grammar has no reading of leaves a tree the printer walks past — and a
 * format over one of those returned the source with part of it gone, with nothing said.
 *
 * <p>The input below only has to be something no reading of the language covers; which shape that
 * is says nothing about the property. A grammar that grows a reading for it leaves this needing
 * another such input, and that is the moment to write one rather than to weaken what is held.
 */
class WhatTheFormatterCannotReadIsRefusedRatherThanPartlyReturnedTest {

    /** A construction whose fields were never closed, with a definition written under it. What is
     *  wanted of this is only that no reading of the language covers it. */
    private static final String UNREADABLE = """
            module shop.carrying

            data Ok = { n: Int }

            behavior take : (held: Ok) -> Ok

            let take (held) = Ok { n = 0

            let after = 1
            """;

    @Test
    void sourceWithASyntaxErrorIsRefused() {
        assertTrue(!CstParser.parse(UNREADABLE).errors().isEmpty(),
                "this is source the parser has something to say about");

        assertThrows(IllegalArgumentException.class, () -> Formatter.format(UNREADABLE),
                "and a format of it does not answer");
    }

    /**
     * And nothing that does come back has lost a token.
     *
     * <p>Held over the code tokens rather than over the text. What a format moves is the whitespace
     * and the line breaks, so comparing the texts would be comparing it against not having run; the
     * tokens are what the source says, and a canonical form says the same thing.
     */
    @Test
    void whatIsFormattedKeepsEveryCodeTokenItWasGiven() {
        String readable = UNREADABLE.replace("let take (held) = Ok { n = 0",
                "let take (held) = Ok { n = 0 }");

        assertEquals(codeTokens(readable), codeTokens(Formatter.format(readable)));
    }

    /** The tokens that carry what the source says, which is every one that is not layout. */
    private static List<String> codeTokens(String source) {
        List<String> out = new ArrayList<>();
        for (GreenToken token : CstLexer.lex(source).tokens()) {
            if (token.kind() != SyntaxKind.WHITESPACE && token.kind() != SyntaxKind.EOF) {
                out.add(token.text());
            }
        }
        return out;
    }
}
