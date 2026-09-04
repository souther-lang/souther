package souther.compiler.fmt;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A token the document lays out is one token of the output, in the place the output has it. This is
 * what says the document represents what is written rather than something that renders to it: a
 * leaf spelling two tokens at once, or one the renderer drops, is a leaf the spacing rule cannot
 * see across, and issue #476 is about not having any of those.
 *
 * <p>The whole sequence, both ways. There is nothing else the document can hold: a leaf spelling
 * more than one token cannot be built, so what the formatter writes is tokens and the boundaries
 * between them, and lexing what that renders to has to give the same tokens back.
 *
 * <p>What it does not say is that the output holds everything the source did. A brace the formatter
 * never emitted is missing from the document and from the output alike and this check passes; that
 * one is the golden corpus's to catch.
 */
@Tag("population")
class EveryTokenTheDocumentLaysOutIsOneTokenOfTheOutputTest {

    /** Every token of {@code doc}, in the order it is laid out. */
    private static List<TokenDoc.Token> laidOut(TokenDoc doc) {
        List<TokenDoc.Token> out = new ArrayList<>();
        collect(doc, out);
        return out;
    }

    /** Every arm is written out and none of them is a {@code default}: a document that grows a way
     *  of holding a token has to be answered for here, and a {@code default} would take the new one
     *  as holding none. */
    private static void collect(TokenDoc doc, List<TokenDoc.Token> out) {
        switch (doc) {
            case TokenDoc.Token t -> out.add(t);
            case TokenDoc.Node n -> collect(n.doc(), out);
            case TokenDoc.At a -> collect(a.doc(), out);
            case TokenDoc.Nest n -> collect(n.doc(), out);
            case TokenDoc.Group g -> collect(g.doc(), out);
            case TokenDoc.Concat c -> c.parts().forEach(part -> collect(part, out));
            case TokenDoc.Nil _, TokenDoc.Comment _, TokenDoc.Trailing _, TokenDoc.Gap _,
                    TokenDoc.MustBreak _, TokenDoc.PointOf _ -> { }
            case TokenDoc.Carries c -> throw new IllegalStateException(
                    "the document under test still holds an unanswered carrier: " + c);
            case TokenDoc.Vacant v -> throw new IllegalStateException(
                    "the document under test still holds brackets nobody has filled: " + v);
        }
    }

    /** Every code token of a source, in the order it is written. */
    private static List<SyntaxToken> written(String source) {
        List<SyntaxToken> out = new ArrayList<>();
        gather(CstParser.parse(source).root(), out);
        return out.stream().filter(t -> !t.isTrivia() && t.kind() != SyntaxKind.EOF).toList();
    }

    private static void gather(SyntaxNode n, List<SyntaxToken> out) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                gather(c, out);
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
    }

    @Test
    void theyAreTheTokensOfTheOutput() {
        List<String> wrong = new ArrayList<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            List<TokenDoc.Token> laid = laidOut(Formatter.canonicalize(CstParser.parse(source).root()).construction().doc());
            List<SyntaxToken> output = written(Formatter.format(source));
            if (laid.size() != output.size()) {
                wrong.add("the document lays out " + laid.size() + " tokens and the output has "
                        + output.size());
                continue;
            }
            for (int i = 0; i < laid.size(); i++) {
                if (laid.get(i).kind() != output.get(i).kind()
                        || !laid.get(i).lexeme().equals(output.get(i).text())) {
                    wrong.add("token " + i + " is " + laid.get(i).kind() + " ["
                            + laid.get(i).lexeme() + "] in the document and " + output.get(i).kind()
                            + " [" + output.get(i).text() + "] in the output");
                    break;
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /** And the check is not passing on an empty hand. */
    @Test
    void theConstructsMovedSoFarLayTheirTokensOut() {
        String source = """
                module some.place exposing ( f )

                behavior pipeline = first >-> second -> Int

                behavior b : (a: Int) -> R
                    constructs Mod.R, S

                let f (o: Option<W>): Int = match o with
                    | Mod.None { a, b = c } as whole -> 0
                    | Some(W(x)) -> x

                let spread (p: P): R = R { ...p.inner, b = 1 }
                """;
        Set<String> laid = new LinkedHashSet<>();
        for (TokenDoc.Token t : laidOut(Formatter.canonicalize(CstParser.parse(source).root()).construction().doc())) {
            laid.add(t.kind() + " " + t.lexeme());
        }
        for (String token : List.of(
                "IDENT some", "DOT .", "IDENT place",     // a name written through its module
                "IDENT first", "IDENT second",            // a pipeline's stages
                "IDENT Mod", "IDENT R",                   // the names a constructs clause lists
                "SPREAD ...", "IDENT inner",              // what a spread names
                "IDENT None", "LBRACE {", "ASSIGN =",     // a match arm's pattern
                "AS_KW as", "LPAREN (", "RPAREN )")) {
            assertTrue(laid.contains(token), "nothing lays out " + token + "; laid out: " + laid);
        }
    }

    /** And what those constructs write is what they wrote before they were moved. */
    @Test
    void andTheyWriteWhatTheyWroteBefore() {
        String canonical = Formatter.format("""
                module some.place

                let f (o: Option<W>): Int = match o with
                    | Mod.None { a, b = c } as whole -> 0
                    | Some(W(x)) -> x

                let spread (p: P): R = R { ...p.inner, b = 1 }
                """);
        for (String written : List.of(
                "module some.place",
                "| Mod.None { a, b = c } as whole -> 0",
                "| Some(W(x)) -> x",
                "R { ...p.inner, b = 1 }")) {
            assertTrue(canonical.contains(written),
                    "nothing holds `" + written + "` in:\n" + canonical);
        }
    }
}
