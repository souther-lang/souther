package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static souther.compiler.fmt.TokenDoc.HARD_GAP;
import static souther.compiler.fmt.TokenDoc.concat;
import static souther.compiler.fmt.TokenDoc.group;
import static souther.compiler.fmt.TokenDoc.nest;

/**
 * A single-canonical-form (gofmt-style) formatter over the concrete syntax tree. It re-derives the
 * layout from the tree's structure and a fixed style — a product type as a leading-comma block, a
 * record literal as a trailing-comma {@code Type { ... }}, a {@code |>} pipeline one stage per line —
 * choosing inline or broken by whether the construct fits {@link #WIDTH} columns. Full-line comments
 * are kept above the construct they precede; blank lines between top-level items collapse to one.
 */
public final class Formatter {

    private static final int INDENT = 4;

    private static final TokenDoc LPAREN = TokenDoc.token(SyntaxKind.LPAREN, "(");
    private static final TokenDoc RPAREN = TokenDoc.token(SyntaxKind.RPAREN, ")");
    private static final TokenDoc LBRACE = TokenDoc.token(SyntaxKind.LBRACE, "{");
    private static final TokenDoc RBRACE = TokenDoc.token(SyntaxKind.RBRACE, "}");
    private static final TokenDoc LBRACKET = TokenDoc.token(SyntaxKind.LBRACKET, "[");
    private static final TokenDoc RBRACKET = TokenDoc.token(SyntaxKind.RBRACKET, "]");
    private static final TokenDoc LT = TokenDoc.token(SyntaxKind.LT, "<");
    private static final TokenDoc GT = TokenDoc.token(SyntaxKind.GT, ">");
    private static final TokenDoc COMMA = TokenDoc.token(SyntaxKind.COMMA, ",");
    private static final TokenDoc DOT = TokenDoc.token(SyntaxKind.DOT, ".");
    private static final TokenDoc QUESTION = TokenDoc.token(SyntaxKind.QUESTION, "?");
    private static final TokenDoc ASSIGN = TokenDoc.token(SyntaxKind.ASSIGN, "=");
    private static final TokenDoc COLON = TokenDoc.token(SyntaxKind.COLON, ":");
    private static final TokenDoc ARROW = TokenDoc.token(SyntaxKind.ARROW, "->");
    private static final TokenDoc PIPE = TokenDoc.token(SyntaxKind.PIPE, "|");
    private static final TokenDoc GAP = TokenDoc.GAP;
    private static final TokenDoc SOFT_GAP = TokenDoc.SOFT_GAP;

    /** The canonical width. It applies to every breakable construct, a declaration's as much as an
     * expression's: a module header that lists more names than fit breaks the same way a call with
     * more arguments than fit does. A line wider than this is one whose content has no separator to
     * break at — a long pattern, a single long token, or a nesting deep enough that the indent alone
     * takes the width. */
    private static final int WIDTH = 100;

    /** The comments taken by some construct, by where they are in the source. A comment is reachable
     * two ways once members nest — from the parent's child list and from the front of the member's
     * own subtree — and it must be written once. The offset identifies a comment without depending on
     * how the tree hands nodes back. It records what was consumed rather than what reached the
     * output, which is what makes it comparable against the comments the tree holds. One instance
     * formats one file, so this lives as long as that. */
    private final java.util.Set<Integer> consumedComments = new java.util.HashSet<>();

    /** Where each of the file's comments goes, decided once before any of it is written. One
     * instance formats one file, so this lives exactly as long as the tree it describes. */
    private Attachments comments = Attachments.empty();

    private Formatter() {
    }

    /** Formats source text into its canonical form. Assumes the source parses without syntax errors;
     * a caller that cannot assume that should check {@link CstParser#parse} first. */
    public static String format(String source) {
        try {
            return format(CstParser.parse(source).root());
        } catch (StackOverflowError _) {
            throw tooDeep();   // the descent that found the end of the stack was the parse's own
        }
    }

    /**
     * The comments {@code file} holds that {@code consumed} does not — the ones the formatter found
     * and did not write. {@link SyntaxKind#LINE_COMMENT} is the only kind of comment the grammar
     * has, so this is all of them.
     */
    static List<SyntaxToken> unconsumed(SyntaxNode file, java.util.Set<Integer> consumed) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxToken t : tokens(file)) {
            if (t.kind() == SyntaxKind.LINE_COMMENT && !consumed.contains(t.start())) {
                out.add(t);
            }
        }
        return out;
    }

    /** Formats an already-parsed file into its canonical form — for a caller that has parsed the
     * source (e.g. to check for syntax errors) and need not parse it again. Assumes {@code file}
     * came from a clean parse. */
    public static String format(SyntaxNode file) {
        try {
            Formatter formatter = new Formatter();
            TokenDoc doc = formatter.file(file);
            List<SyntaxToken> missing = unconsumed(file, formatter.consumedComments);
            if (!missing.isEmpty()) {
                throw new IllegalStateException(
                        missing.size() + " comment(s) in this source reached no construct and would"
                                + " have been dropped; the first is at offset "
                                + missing.get(0).start() + ": "
                                + missing.get(0).text().stripTrailing());
            }
            return doc.resolve().render(WIDTH);
        } catch (StackOverflowError _) {
            throw tooDeep();
        }
    }

    /**
     * The document this formatter builds for {@code file}. For a test that has to see the tokens
     * the formatter lays out rather than the text they render to — what is written between two of
     * them is decided from the document, so a check on that decision reads the document.
     */
    static TokenDoc document(SyntaxNode file) {
        return new Formatter().file(file);
    }

    /**
     * A tree that nests deeper than this walk can descend. {@link CstParser} bounds what it builds,
     * so a tree from a parse this compiler ran does not reach here; what does is a thread with less
     * stack than that bound was set for, and a {@code StackOverflowError} is not a
     * {@link CompileException}, so left alone it passes through the recovery boundary and reaches
     * the author as a stack trace.
     *
     * <p>No position is claimed: unlike the parser's limit, this one was not reached at a token —
     * it was reached wherever the stack happened to end, which is not a fact about the source.
     */
    private static CompileException tooDeep() {
        return CompileException.of(
                Diagnostic.of(DiagnosticCode.E2104, "parse.toodeep").build(),
                "this source nests too deeply to format;"
                        + " break the nesting into named parts to flatten it");
    }

    // --- layout ---
    //
    // Every repeated or joined construct is written through these, so the separator of a construct
    // is a place the layout may break rather than a literal the construct spelled itself. A
    // construct that spells its own separators is one the width cannot reach: the break has to exist
    // in the document before the renderer can choose it, and the renderer breaks the outermost group
    // that does not fit, so a member is split only when the structure around it had nothing to give.

    /**
     * A member and the comment written at the end of the line it takes. The comment goes after
     * whatever the enclosing construct writes between this member and the next, because that
     * punctuation is on this line too — a comma written after the comment would be inside it.
     */
    private record Member(TokenDoc doc, TokenDoc trailing) {}

    /** Members that carry no comment of their own. */
    private static List<Member> plain(List<TokenDoc> docs) {
        List<Member> out = new ArrayList<>();
        for (TokenDoc d : docs) {
            out.add(new Member(d, TokenDoc.NIL));
        }
        return out;
    }

    /** Members with a comma between them, one to a line where they do not fit. The comma stays on
     * the line its member ends, and a comment written at the end of that line follows the comma. */
    private static TokenDoc separated(List<Member> members) {
        List<TokenDoc> parts = new ArrayList<>();
        for (int i = 0; i < members.size(); i++) {
            if (i > 0) {
                parts.add(SOFT_GAP);
            }
            parts.add(members.get(i).doc());
            if (i < members.size() - 1) {
                parts.add(GAP);
                parts.add(COMMA);
            }
            parts.add(members.get(i).trailing());
        }
        return concat(parts);
    }

    /**
     * Members between brackets. What sits just inside them is a boundary like any other: the
     * layout may break there, and where it does not, what is written is the rule's answer for the
     * bracket against what stands next to it. It used to be the caller's pick of one line or the
     * other, which made {@code exposing ( a, b )} and {@code f(a, b)} two decisions instead of one.
     *
     * <p>{@code construct} is what the canonical form writes here, which is not always the node the
     * source had: a definition written {@code let f = (x) -> x} is written back as
     * {@code let f (x) = x}, and those brackets are a parameter list in what is read back.
     */
    private static TokenDoc delimited(SyntaxKind construct, TokenDoc open, List<Member> members,
            TokenDoc close) {
        if (members.isEmpty()) {
            // Brackets with nothing between them hold one boundary and not two. Written as two —
            // one just inside each bracket — what a construct written open put there was two
            // spaces, and no rule had said so.
            return TokenDoc.node(construct, concat(open, GAP, close));
        }
        return TokenDoc.node(construct, group(concat(open,
                nest(INDENT, concat(SOFT_GAP, separated(members))),
                SOFT_GAP, close)));
    }

    /**
     * One part of a chain, written after the connector that joins it to what came before.
     * {@code leading} is what goes above the line the part opens — its comments. The connector is
     * part of that line, so the two are written in this order and not the other: a comment placed
     * after the connector leaves the part itself starting a line the connector never opened.
     */
    private record Segment(TokenDoc connector, TokenDoc doc, TokenDoc leading) {}

    /**
     * A part of a chain that something in the source stands for. Every segment of every chain is
     * built here: a chain is written from what the source holds, and one built without asking what
     * was written above and beside it is one whose comments have nowhere to go. {@code owner} is
     * null only where the source has nothing there — an example row with no expected value.
     */
    private Segment segment(TokenDoc connector, SyntaxNode owner, TokenDoc doc) {
        return owner == null
                ? new Segment(connector, doc, TokenDoc.NIL)
                : new Segment(connector, concat(doc, afterOf(owner)), aboveOf(owner));
    }

    /** The same for a part the grammar writes as a bare identifier rather than as a node — a sum's
     * cases. It is the only other way a chain's part can stand for something written, so between the
     * two of them nothing else builds a {@link Segment}. */
    private Segment segment(TokenDoc connector, SyntaxToken owner, TokenDoc doc) {
        List<TokenDoc> lead = new ArrayList<>();
        for (TokenDoc c : aboveCase(owner)) {
            lead.add(concat(c, HARD_GAP));
        }
        return new Segment(connector, concat(doc, afterCase(owner)), concat(lead));
    }

    /**
     * A head and the parts written after it, each opening with its connector — a union's {@code |},
     * an operator chain's operator, a pipeline's {@code |>}, an example row's {@code :} and
     * {@code ->}. Broken, each part starts a line one indent in and the connector leads it, so what
     * joins two parts is visible at the front of the second.
     */
    private static TokenDoc chained(Member head, List<Segment> segments) {
        List<TokenDoc> parts = new ArrayList<>();
        for (Segment s : segments) {
            parts.add(concat(SOFT_GAP, s.leading(), s.connector(), GAP, s.doc()));
        }
        return group(concat(head.doc(), head.trailing(), nest(INDENT, concat(parts))));
    }

    /** The part of a chain written before the first connector, from the construct it stands for. A
     * head is a member like a segment is, and the same three things it can stand for: a node, an
     * identifier, or nothing the source wrote. */
    private Member head(SyntaxNode owner, TokenDoc doc) {
        return new Member(concat(aboveOf(owner), doc), afterOf(owner));
    }

    /** The same for a head the grammar writes as a token — an example row's description, a match
     * arm's pattern. Nothing is read above it: a comment written above one of those, or between the
     * {@code |} and the token itself, is about the row, and the row writes it above its own line. So
     * this head carries only what ends the line it opens. */
    private Member head(SyntaxToken owner, TokenDoc doc) {
        return new Member(doc, afterCase(owner));
    }

    /** A head the source has nothing at — a `fake` row's default `_`. */
    private static Member synthetic(TokenDoc doc) {
        return new Member(doc, TokenDoc.NIL);
    }

    // --- top level ---

    private TokenDoc file(SyntaxNode file) {
        comments = attach(file);
        List<TokenDoc> parts = new ArrayList<>();
        SyntaxKind prev = null;
        for (SyntaxNode item : file.childNodes()) {
            if (!isTopLevel(item.kind())) {
                continue;
            }
            // A top-level item's comments are read the same way a member's are, and marked written
            // the same way: an `example`'s comment is the item's leading trivia here and the first
            // row's from inside, and it belongs to whichever asks first.
            TokenDoc lead = aboveOf(item);
            if (prev != null) {
                parts.add(HARD_GAP);
                if (blankBetween(prev, item.kind())) {
                    parts.add(HARD_GAP);
                }
            }
            parts.add(lead);
            parts.add(item(item));
            parts.add(afterOf(item));
            prev = item.kind();
        }
        parts.add(endOf(file));
        parts.add(HARD_GAP);   // files end with a single newline
        return concat(parts);
    }

    /** One blank line separates every top-level item, except the module header and its imports,
     * which stay tight together (as gofmt keeps a package clause and its import block). */
    private static boolean blankBetween(SyntaxKind prev, SyntaxKind current) {
        boolean header = (prev == SyntaxKind.MODULE_HEADER || prev == SyntaxKind.IMPORT_DECL)
                && current == SyntaxKind.IMPORT_DECL;
        return !header;
    }

    /** The kinds {@link #file} writes as items of the file, and so the kinds the separation between
     * two items is a function of. Reachable from a test so that the table of what goes between two
     * of them can be asked whether it covers every pair rather than the pairs someone thought of. */
    static boolean isTopLevel(SyntaxKind k) {
        return k == SyntaxKind.MODULE_HEADER || k == SyntaxKind.IMPORT_DECL
                || k == SyntaxKind.DATA_DEF || k == SyntaxKind.BEHAVIOR_DEF || k == SyntaxKind.FN_DEF
                || k == SyntaxKind.EXAMPLE_DEF || k == SyntaxKind.EXAMPLES_FILE_HEADER
                || k == SyntaxKind.FAKE_DEF;
    }

    private TokenDoc item(SyntaxNode n) {
        return switch (n.kind()) {
            case MODULE_HEADER -> moduleHeader(n);
            case IMPORT_DECL -> importDecl(n);
            case DATA_DEF -> dataDef(n);
            case BEHAVIOR_DEF -> behaviorDef(n);
            case FN_DEF -> fnDef(n);
            case EXAMPLES_FILE_HEADER -> examplesFileHeader(n);
            case EXAMPLE_DEF -> exampleDef(n);
            case FAKE_DEF -> fakeDef(n);
            default -> throw new IllegalStateException("no case writes " + n.kind());
        };
    }

    // --- example ---

    private TokenDoc examplesFileHeader(SyntaxNode n) {
        return TokenDoc.node(n.kind(), concat(ident("examples"), GAP, ident("for"), GAP,
                qualifiedName(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow())));
    }

    private TokenDoc exampleDef(SyntaxNode n) {
        List<SyntaxToken> ids = idents(n);   // ["example", target]
        String target = ids.size() >= 2 ? ids.get(1).text() : "";
        List<TokenDoc> rows = new ArrayList<>();
        for (SyntaxNode row : childNodes(n, SyntaxKind.EXAMPLE_ROW)) {
            rows.add(concat(HARD_GAP, concat(aboveOf(row), exampleRow(row)),
                    afterOf(row)));
        }
        rows.add(endOf(n));
        return TokenDoc.node(n.kind(), concat(ident("example"), GAP, ident(target),
                afterToken(ids.get(ids.size() - 1), ids.size() >= 2), nest(INDENT, concat(rows))));
    }

    /**
     * A row of an example: its description, its input and what it is expected to give. The three are
     * the row's own parts, so the row is what breaks when it does not fit — a row that broke inside
     * its input instead left {@code ), Amount(100)) -> Accepted} opening a line, and stopped showing
     * which part was which.
     */
    private TokenDoc exampleRow(SyntaxNode n) {
        TokenDoc input = n.child(SyntaxKind.ARG_LIST)
                .map(a -> delimited(SyntaxKind.ARG_LIST, LPAREN, exprDocs(a), RPAREN))
                .orElse(concat(LPAREN, GAP, RPAREN));
        var with = n.child(SyntaxKind.WITH_CLAUSE);
        if (with.isPresent()) {
            List<Member> binds = new ArrayList<>();
            for (SyntaxNode b : childNodes(with.get(), SyntaxKind.WITH_BINDING)) {
                binds.add(member(b, TokenDoc.node(b.kind(), concat(ident(firstIdent(b)), GAP,
                        ASSIGN, GAP, expr(firstExprChildOpt(b).orElseThrow())))));
            }
            input = concat(input, GAP, TokenDoc.node(with.get().kind(),
                    concat(TokenDoc.token(SyntaxKind.WITH_KW, "with"), GAP,
                            group(nest(INDENT, separated(withEndComments(with.get(), binds)))))));
        }

        List<Segment> segs = new ArrayList<>();
        var desc = n.token(SyntaxKind.STRING_LIT);
        Member head;
        if (desc.isPresent()) {
            head = head(desc.get(), token(desc.get()));
            segs.add(segment(COLON, n.child(SyntaxKind.ARG_LIST).orElse(null), input));
        } else {
            // with no description the input opens the row, so the row's head carries its comments
            SyntaxNode args = n.child(SyntaxKind.ARG_LIST).orElse(null);
            head = args == null ? synthetic(input) : head(args, input);
        }
        List<SyntaxNode> expected = exprChildren(n);   // the row's expr child that is not the ARG_LIST
        segs.add(segment(ARROW, expected.isEmpty() ? null : expected.get(0),
                expected.isEmpty() ? TokenDoc.NIL : expr(expected.get(0))));
        return concat(PIPE, GAP, TokenDoc.node(n.kind(), chained(head, segs)));
    }

    private TokenDoc fakeDef(SyntaxNode n) {
        List<SyntaxToken> ids = idents(n);   // ["fake", target]
        String target = ids.size() >= 2 ? ids.get(1).text() : "";
        List<TokenDoc> rows = new ArrayList<>();
        for (SyntaxNode row : childNodes(n, SyntaxKind.FAKE_ROW)) {
            rows.add(concat(HARD_GAP, concat(aboveOf(row), fakeRow(row)), afterOf(row)));
        }
        rows.add(endOf(n));
        return TokenDoc.node(n.kind(), concat(ident("fake"), GAP, ident(target),
                afterToken(ids.get(ids.size() - 1), ids.size() >= 2), nest(INDENT, concat(rows))));
    }

    private TokenDoc fakeRow(SyntaxNode n) {
        var args = n.child(SyntaxKind.ARG_LIST);
        TokenDoc input;
        if (args.isPresent()) {
            input = delimited(SyntaxKind.ARG_LIST, LPAREN, exprDocs(args.get()), RPAREN);
        } else {
            input = ident("_");   // the default row
        }
        List<SyntaxNode> outs = exprChildren(n);
        // the input opens the row, so the head carries what was written above and beside it
        Member head = args.map(a -> head(a, input)).orElse(synthetic(input));
        return concat(PIPE, GAP, TokenDoc.node(n.kind(), chained(head,
                List.of(segment(ARROW, outs.isEmpty() ? null : outs.get(0),
                        outs.isEmpty() ? TokenDoc.NIL : expr(outs.get(0)))))));
    }

    private TokenDoc moduleHeader(SyntaxNode n) {
        TokenDoc d = concat(TokenDoc.token(SyntaxKind.MODULE_KW, "module"), GAP,
                qualifiedName(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow()));
        return TokenDoc.node(n.kind(), n.child(SyntaxKind.EXPOSING_CLAUSE)
                .map(c -> concat(d, GAP, exposing(c)))
                .orElse(d));
    }

    private TokenDoc exposing(SyntaxNode clause) {
        List<Member> entries = new ArrayList<>();
        for (SyntaxNode e : childNodes(clause, SyntaxKind.EXPOSED_ENTRY)) {
            TokenDoc name = qualifiedName(e.child(SyntaxKind.QUALIFIED_NAME).orElseThrow());
            entries.add(member(e, TokenDoc.node(e.kind(), e.child(SyntaxKind.RET_TYPE)
                    .map(rt -> concat(name, GAP, COLON, GAP, retType(rt)))
                    .orElse(name))));
        }
        return delimited(SyntaxKind.EXPOSING_CLAUSE, concat(TokenDoc.token(SyntaxKind.EXPOSING_KW, "exposing"), GAP,
                LPAREN), withEndComments(clause, entries), RPAREN);
    }

    private TokenDoc importDecl(SyntaxNode n) {
        TokenDoc d = concat(TokenDoc.token(SyntaxKind.IMPORT_KW, "import"), GAP,
                qualifiedName(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow()));
        Optional<SyntaxNode> alias = n.child(SyntaxKind.IMPORT_ALIAS);
        if (alias.isPresent()) {
            d = concat(d, GAP, TokenDoc.node(alias.get().kind(),
                    concat(TokenDoc.token(SyntaxKind.AS_KW, "as"), GAP,
                            token(idents(alias.get()).get(0)))));
        }
        Optional<SyntaxNode> list = n.child(SyntaxKind.NAME_LIST);
        if (list.isEmpty()) {
            return TokenDoc.node(n.kind(), d);   // one that only renames it, or only names it
        }
        List<Member> names = new ArrayList<>();
        for (SyntaxToken t : idents(list.get())) {
            names.add(tokenMember(t, t, token(t)));
        }
        return TokenDoc.node(n.kind(), concat(d, GAP,
                delimited(SyntaxKind.NAME_LIST, LPAREN, withEndComments(list.get(), names), RPAREN)));
    }

    // --- data ---

    private TokenDoc dataDef(SyntaxNode n) {
        String name = firstIdent(n);
        List<TokenDoc> invariants = new ArrayList<>();
        for (SyntaxNode inv : childNodes(n, SyntaxKind.INVARIANT_CLAUSE)) {
            // A named clause keeps its name: it is what an attempt's arm and a boundary issue call it.
            TokenDoc label = inv.token(SyntaxKind.ASSIGN).isPresent()
                    ? concat(ident(firstIdent(inv)), GAP, ASSIGN, GAP) : TokenDoc.NIL;
            invariants.add(concat(HARD_GAP,
                    concat(aboveOf(inv), TokenDoc.node(inv.kind(), concat(TokenDoc.token(SyntaxKind.INVARIANT_KW, "invariant"), GAP, label,
                            expr(onlyExpr(inv))))),
                    afterOf(inv)));
        }

        var product = n.child(SyntaxKind.PRODUCT_BODY);
        if (product.isPresent()) {
            if (isEmptyProduct(product.get())) {
                return TokenDoc.node(n.kind(),
                        concat(TokenDoc.token(SyntaxKind.DATA_KW, "data"), GAP, ident(name), GAP,
                        ASSIGN, GAP, TokenDoc.node(product.get().kind(), concat(LBRACE, GAP, RBRACE)),
                        afterToken(n.token(SyntaxKind.ASSIGN)),
                        nest(INDENT, concat(invariants))));
            }
            return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.DATA_KW, "data"), GAP, ident(name), GAP, ASSIGN,
                    afterToken(n.token(SyntaxKind.ASSIGN)),
                    nest(INDENT, concat(concat(HARD_GAP, productBody(product.get())),
                            concat(invariants)))));
        }
        var sum = n.child(SyntaxKind.SUM_BODY);
        if (sum.isPresent()) {
            // A sum's cases are bare idents, not nodes, so a case's comments are held against where
            // its identifier is rather than against a member node.
            TokenDoc head = null;
            List<TokenDoc> headComments = new ArrayList<>();
            List<Segment> cases = new ArrayList<>();
            for (SyntaxElement e : sum.get().children()) {
                if (!(e instanceof SyntaxToken t) || t.kind() != SyntaxKind.IDENT) {
                    continue;
                }
                if (head == null) {
                    head = concat(token(t), afterCase(t));
                    headComments = new ArrayList<>();
                    for (TokenDoc c : aboveCase(t)) {
                        headComments.add(concat(c, HARD_GAP));
                    }
                } else {
                    cases.add(segment(PIPE, t, token(t)));
                }
            }
            TokenDoc chain = TokenDoc.node(sum.get().kind(), chained(synthetic(head), cases));
            if (headComments.isEmpty()) {
                return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.DATA_KW, "data"), GAP, ident(name), GAP, ASSIGN, GAP, chain));
            }
            // The first case shares its line with `data S =`, so its comments cannot go above that
            // line without describing the declaration instead. The union moves down a line instead.
            return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.DATA_KW, "data"), GAP, ident(name), GAP, ASSIGN,
                    nest(INDENT, concat(HARD_GAP, concat(headComments), chain))));
        }
        var newtype = n.child(SyntaxKind.NEWTYPE_BODY);
        if (newtype.isPresent()) {
            TokenDoc inner = concat(aboveOf(newtype.get()), typeRef(typeChild(newtype.get())),
                    afterOf(newtype.get()));
            return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.DATA_KW, "data"), GAP, ident(name), GAP, ASSIGN, GAP, inner,
                    nest(INDENT, concat(invariants))));
        }
        return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.DATA_KW, "data"), GAP, ident(name)));   // unit
    }

    /** The leading-comma product block: {@code { f1: T1\n, f2: T2\n}}. Multi-line wherever it holds
     * anything: the block writes its opening brace on the first member's line, so a body with no
     * members has no line to write one on, and it is written as the empty brackets it is. */
    private TokenDoc productBody(SyntaxNode body) {
        List<TokenDoc> lines = new ArrayList<>();
        for (SyntaxNode m : body.childNodes()) {
            TokenDoc member;
            if (m.kind() == SyntaxKind.FIELD) {
                member = field(m);
            } else if (m.kind() == SyntaxKind.SPREAD_MEMBER) {
                member = TokenDoc.node(m.kind(), concat(
                        TokenDoc.token(SyntaxKind.SPREAD, "..."), GAP,
                        dottedName(idents(m))));
            } else {
                continue;
            }
            // The opener is part of the member's line, so it is inside what the comments decorate:
            // a comment written after it would leave the member starting a line of its own, at the
            // block's indent rather than after the comma the rest of the block is written with.
            boolean first = lines.isEmpty();
            TokenDoc line = concat(concat(aboveOf(m), first ? LBRACE : COMMA, GAP, member),
                    afterOf(m));
            lines.add(first ? line : concat(HARD_GAP, line));
        }
        if (lines.isEmpty()) {
            // No member wrote the opening brace, so the block writes it on a line of its own. This
            // is the body that holds only comments: `dataDef` writes a body holding nothing at all
            // as `{}` and never reaches here.
            lines.add(LBRACE);
        }
        lines.add(endOf(body));
        lines.add(concat(HARD_GAP, RBRACE));
        return TokenDoc.node(body.kind(), concat(lines));
    }

    /**
     * Whether {@code body} has nothing for the block to write a line for. A body holding only
     * comments is not empty: they are written where a member would be, so the block keeps its lines.
     *
     * <p>Asked of the attachments rather than through {@link #endLines}, which takes the comments it
     * reports. A question about what is there has to leave it there for whoever writes it.
     */
    private boolean isEmptyProduct(SyntaxNode body) {
        for (SyntaxNode m : body.childNodes()) {
            if (m.kind() == SyntaxKind.FIELD || m.kind() == SyntaxKind.SPREAD_MEMBER) {
                return false;
            }
        }
        return comments.atEnd().getOrDefault(body, List.of()).isEmpty();
    }

    private TokenDoc field(SyntaxNode n) {
        TokenDoc d = concat(ident(firstIdent(n)), GAP, COLON, GAP, typeRef(typeChild(n)));
        return TokenDoc.node(n.kind(),
                n.token(SyntaxKind.QUESTION).isPresent() ? concat(d, GAP, QUESTION) : d);
    }

    // --- behavior ---

    private TokenDoc behaviorDef(SyntaxNode n) {
        String name = firstIdent(n);
        var sig = n.child(SyntaxKind.BEHAVIOR_SIG);
        if (sig.isPresent()) {
            SyntaxNode s = sig.get();
            TokenDoc params = paramList(s.child(SyntaxKind.PARAM_LIST).orElseThrow());
            SyntaxNode retNode = s.child(SyntaxKind.RET_TYPE).orElseThrow();
            TokenDoc ret = concat(aboveOf(retNode), retType(retNode), afterOf(retNode));
            List<TokenDoc> clauses = new ArrayList<>();
            for (SyntaxNode c : s.childNodes()) {
                if (c.kind() == SyntaxKind.CONSTRUCTS_CLAUSE) {
                    clauses.add(concat(HARD_GAP, concat(aboveOf(c), TokenDoc.node(c.kind(),
                            concat(TokenDoc.token(SyntaxKind.CONSTRUCTS_KW, "constructs"), GAP,
                                    nameList(c, 0)))), afterOf(c)));
                } else if (c.kind() == SyntaxKind.DEPENDS_CLAUSE) {
                    clauses.add(concat(HARD_GAP, concat(aboveOf(c), TokenDoc.node(c.kind(),
                            concat(TokenDoc.token(SyntaxKind.DEPENDS_KW, "depends"), GAP,
                                    ident("on"), GAP, nameList(c, 1)))), afterOf(c)));
                }
            }
            return TokenDoc.node(n.kind(),
                    concat(TokenDoc.token(SyntaxKind.BEHAVIOR_KW, "behavior"), GAP, ident(name),
                            GAP, COLON, GAP, TokenDoc.node(s.kind(), concat(params, GAP, ARROW, GAP,
                                    ret, nest(INDENT, concat(clauses))))));
        }
        SyntaxNode pipe = n.child(SyntaxKind.PIPE_BEHAVIOR).orElseThrow();
        List<SyntaxNode> stages = childNodes(pipe, SyntaxKind.STAGE);
        TokenDoc declaredOut = pipe.child(SyntaxKind.RET_TYPE)
                .map(rt -> concat(GAP, ARROW, GAP, retType(rt))).orElse(TokenDoc.NIL);
        List<TokenDoc> parts = new ArrayList<>();
        for (int i = 0; i < stages.size(); i++) {
            SyntaxNode st = stages.get(i);
            // What the declaration writes after the last stage is on that stage's line, so it comes
            // before the comment that ends the line rather than after it.
            parts.add(concat(SOFT_GAP, aboveOf(st),
                    i == 0 ? TokenDoc.NIL : concat(TokenDoc.token(SyntaxKind.PIPEFWD, ">->"), GAP), stage(st),
                    i == stages.size() - 1 ? declaredOut : TokenDoc.NIL, afterOf(st)));
        }
        return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.BEHAVIOR_KW, "behavior"), GAP, ident(name), GAP, ASSIGN,
                TokenDoc.node(pipe.kind(), group(nest(INDENT, concat(parts))))));
    }

    private TokenDoc paramList(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode p : childNodes(n, SyntaxKind.PARAM)) {
            params.add(member(p, TokenDoc.node(p.kind(), concat(ident(firstIdent(p)), GAP, COLON,
                    GAP, retType(p.child(SyntaxKind.RET_TYPE).orElseThrow())))));
        }
        return delimited(SyntaxKind.PARAM_LIST, LPAREN, withEndComments(n, params), RPAREN);
    }

    /** One stage of a pipeline, which is a name and is written as one. */
    private TokenDoc stage(SyntaxNode n) {
        return qualifiedName(n);
    }

    /** The names a {@code constructs} / {@code depends on} clause lists. {@code skipIdents} drops
     * the leading identifiers that belong to the keyword rather than the list — the {@code on} of
     * {@code depends on}, which lexes as an ordinary identifier. */
    private TokenDoc nameList(SyntaxNode clause, int skipIdents) {
        // an entry may name through a module, so the dots of one name are kept and only a comma
        // starts the next
        List<Member> names = new ArrayList<>();
        List<SyntaxToken> current = new ArrayList<>();
        int skipped = 0;
        for (SyntaxElement e : meaningful(clause)) {
            if (!(e instanceof SyntaxToken t)) {
                continue;
            }
            if (t.kind() == SyntaxKind.IDENT && skipped < skipIdents) {
                skipped++;
                continue;
            }
            switch (t.kind()) {
                case IDENT -> current.add(t);
                case COMMA -> {
                    names.add(named(clause, current));
                    current = new ArrayList<>();
                }
                default -> { }   // the dots of one name, and the `constructs` / `depends` keyword
            }
        }
        if (!current.isEmpty()) {
            names.add(named(clause, current));
        }
        return TokenDoc.node(clause.kind(),
                group(nest(INDENT, separated(withEndComments(clause, names)))));
    }

    /** One name of such a clause, held against where its identifiers are. */
    private Member named(SyntaxNode clause, List<SyntaxToken> idents) {
        return tokenMember(idents.get(0), idents.get(idents.size() - 1), dottedName(idents));
    }

    /** The {@code : T} a node wrote, or nothing — a helper's return type, a local binding's annotation. */
    private TokenDoc writtenType(SyntaxNode n) {
        return n.child(SyntaxKind.RET_TYPE)
                .map(rt -> concat(GAP, COLON, GAP, retType(rt))).orElse(TokenDoc.NIL);
    }

    // --- fn ---

    private TokenDoc fnDef(SyntaxNode n) {
        String name = firstIdent(n);
        // The modifiers are written back in the order the parser reads them: `private partial let`.
        List<TokenDoc> modifiers = new ArrayList<>();
        if (n.child(SyntaxKind.PRIVATE_MODIFIER).isPresent()) {
            modifiers.add(concat(ident("private"), GAP));
        }
        if (n.child(SyntaxKind.PARTIAL_MODIFIER).isPresent()) {
            modifiers.add(concat(ident("partial"), GAP));
        }
        TokenDoc keyword = concat(concat(modifiers), TokenDoc.token(SyntaxKind.LET_KW, "let"), GAP);
        var written = n.child(SyntaxKind.FN_PARAM_LIST);
        // A lambda on the right of `=` is the parameter-list form written the other way round, so it
        // is written back with its parameters on the left. A definition with neither is a value, and
        // writes no list at all.
        SyntaxNode lifted = written.isPresent() ? null : liftedLambda(n);
        TokenDoc params = written.isPresent() ? concat(GAP, fnParamList(written.get()))
                : lifted == null ? TokenDoc.NIL : concat(GAP, lambdaParams(lifted));
        TokenDoc head = concat(keyword, ident(name), params, writtenType(n));

        var intrinsic = n.child(SyntaxKind.INTRINSIC_BODY);
        if (intrinsic.isPresent()) {
            SyntaxToken body = intrinsic.get().token(SyntaxKind.STRING_LIT).orElseThrow();
            return TokenDoc.node(n.kind(), concat(head, GAP, ASSIGN,
                    group(nest(INDENT, concat(SOFT_GAP, TokenDoc.node(intrinsic.get().kind(),
                            concat(ident("intrinsic"), GAP, token(body))))))));
        }
        var block = n.child(SyntaxKind.BLOCK_EXPR);
        if (block.isPresent()) {
            return TokenDoc.node(n.kind(), concat(head, GAP, ASSIGN, GAP, block(block.get())));
        }
        SyntaxNode body = lifted == null ? onlyExpr(n) : lastExprChild(lifted);
        return TokenDoc.node(n.kind(),
                concat(head, GAP, ASSIGN, group(nest(INDENT, concat(SOFT_GAP, expr(body))))));
    }

    /** The lambda a parameter-less definition was written as, or null when its body is an ordinary
     * expression and the definition is a value. */
    private SyntaxNode liftedLambda(SyntaxNode n) {
        if (n.child(SyntaxKind.BLOCK_EXPR).isPresent() || n.child(SyntaxKind.INTRINSIC_BODY).isPresent()) {
            return null;
        }
        // A written function type moves nothing. It says what the definition is, and what it says is
        // a function, so the definition is a value of that type; lifting its parameters out would
        // leave the written type describing something the definition is no longer. The frontend
        // reads such a definition as a value for the same reason, and a definition the two of them
        // read differently is one whose canonical form does not compile.
        if (writesAFunctionType(n)) {
            return null;
        }
        SyntaxNode body = onlyExpr(n);
        return body.kind() == SyntaxKind.LAMBDA_EXPR ? body : null;
    }

    /** Whether a definition's written type is a lone function type. This is what the frontend asks
     * of the type it built ({@code Ast.RetType.asFn}), asked of the syntax instead: a sum of a
     * function with anything else is not one, an optional is a type of its own, and a single term in
     * parentheses is the term. */
    private static boolean writesAFunctionType(SyntaxNode n) {
        Optional<SyntaxNode> written = n.child(SyntaxKind.RET_TYPE);
        if (written.isEmpty() || written.get().token(SyntaxKind.QUESTION).isPresent()) {
            return false;
        }
        List<SyntaxNode> cases = typeTerms(written.get());
        return cases.size() == 1 && isFunctionType(cases.get(0));
    }

    private static boolean isFunctionType(SyntaxNode type) {
        if (type.kind() == SyntaxKind.FN_TYPE) {
            return true;
        }
        List<SyntaxNode> elements = typeTerms(type);
        return type.kind() == SyntaxKind.TUPLE_TYPE && elements.size() == 1
                && isFunctionType(elements.get(0));
    }

    private static List<SyntaxNode> typeTerms(SyntaxNode n) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isTypeNode(c.kind())) {
                out.add(c);
            }
        }
        return out;
    }

    /** A lambda's parameters as a definition's parameter list — always parenthesised, which is the
     * only shape a definition writes. */
    private TokenDoc lambdaParams(SyntaxNode lambda) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode c : lambda.childNodes()) {
            if (isPatternNode(c.kind())) {
                params.add(member(c, pattern(c)));
            }
        }
        return delimited(SyntaxKind.FN_PARAM_LIST, LPAREN, withEndComments(lambda, params), RPAREN);
    }

    private TokenDoc fnParamList(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode p : childNodes(n, SyntaxKind.FN_PARAM)) {
            SyntaxNode pat = optionalPatternChild(p);
            TokenDoc d = pat == null ? ident(firstIdent(p)) : pattern(pat);
            var rt = p.child(SyntaxKind.RET_TYPE);
            if (rt.isPresent()) {
                d = concat(d, GAP, COLON, GAP, retType(rt.get()));
            }
            params.add(member(p, TokenDoc.node(p.kind(), d)));
        }
        return delimited(SyntaxKind.FN_PARAM_LIST, LPAREN, withEndComments(n, params), RPAREN);
    }

    // --- types ---

    private TokenDoc fnType(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        TokenDoc result = TokenDoc.NIL;
        boolean afterArrow = false;
        for (SyntaxElement e : meaningful(n)) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.ARROW) {
                afterArrow = true;
            } else if (e instanceof SyntaxNode c && c.kind() == SyntaxKind.RET_TYPE) {
                if (afterArrow) {
                    result = concat(aboveOf(c), retType(c), afterOf(c));
                } else {
                    params.add(member(c, retType(c)));
                }
            }
        }
        return TokenDoc.node(n.kind(),
                concat(delimited(SyntaxKind.FN_TYPE, LPAREN, withEndComments(n, params), RPAREN),
                        GAP, ARROW, GAP, result));
    }

    private TokenDoc retType(SyntaxNode n) {
        List<TokenDoc> cases = new ArrayList<>();
        List<Segment> rest = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (!isTypeNode(c.kind())) {
                continue;
            }
            TokenDoc body = concat(typeTerm(c), afterOf(c));
            if (cases.isEmpty()) {
                cases.add(concat(aboveOf(c), body));
            } else {
                rest.add(segment(PIPE, c, typeTerm(c)));
            }
        }
        TokenDoc d = cases.isEmpty() ? TokenDoc.NIL
                : TokenDoc.node(n.kind(), chained(synthetic(cases.get(0)), rest));
        // `T?` in a core signature, the same mark a field carries
        return n.token(SyntaxKind.QUESTION).isPresent()
                ? TokenDoc.node(n.kind(), concat(d, GAP, QUESTION)) : d;
    }

    private TokenDoc typeRef(SyntaxNode n) {
        if (n.kind() == SyntaxKind.TUPLE_TYPE) {
            List<Member> elems = new ArrayList<>();
            for (SyntaxNode c : n.childNodes()) {
                if (isTypeNode(c.kind())) {
                    elems.add(member(c, typeTerm(c)));
                }
            }
            return delimited(SyntaxKind.TUPLE_TYPE, LPAREN, withEndComments(n, elems), RPAREN);
        }
        var typevar = n.token(SyntaxKind.TYPEVAR);
        if (typevar.isPresent()) {
            return token(typevar.get());
        }
        TokenDoc name = qualifiedName(n);   // a type may be named through its module or an import alias
        var args = n.child(SyntaxKind.TYPE_ARGS);
        if (args.isEmpty()) {
            return name;
        }
        List<Member> typeArgs = new ArrayList<>();
        for (SyntaxNode c : args.get().childNodes()) {
            if (isTypeNode(c.kind())) {
                typeArgs.add(member(c, typeTerm(c)));
            }
        }
        return TokenDoc.node(n.kind(), concat(name, GAP,
                delimited(SyntaxKind.TYPE_ARGS, LT, withEndComments(args.get(), typeArgs), GT)));
    }

    private static boolean isTypeNode(SyntaxKind k) {
        return k == SyntaxKind.TYPE_REF || k == SyntaxKind.TUPLE_TYPE || k == SyntaxKind.FN_TYPE;
    }

    /** One term of a written type. A function type reads as itself wherever a type goes. */
    private TokenDoc typeTerm(SyntaxNode n) {
        return n.kind() == SyntaxKind.FN_TYPE ? fnType(n) : typeRef(n);
    }

    // --- expressions ---

    private TokenDoc expr(SyntaxNode n) {
        return switch (n.kind()) {
            case LITERAL_EXPR -> token(firstMeaningfulToken(n));
            case VAR_EXPR -> ident(firstIdent(n));
            case FIELD_ACCESS -> TokenDoc.node(n.kind(),
                    concat(expr(firstExprChild(n)), GAP, DOT, GAP, ident(lastIdent(n))));
            case FIELD_GETTER -> TokenDoc.node(n.kind(), concat(DOT, GAP, ident(lastIdent(n))));
            case APPLY_EXPR -> apply(n);
            case BINARY_EXPR -> binary(n);
            case UNARY_EXPR -> TokenDoc.node(n.kind(),
                    concat(TokenDoc.token(SyntaxKind.MINUS, "-"), GAP, expr(onlyExpr(n))));
            case PIPE_EXPR -> pipe(n);
            case PAREN_EXPR -> TokenDoc.node(n.kind(),
                    concat(LPAREN, GAP, expr(onlyExpr(n)), GAP, RPAREN));
            case TUPLE_EXPR -> delimited(SyntaxKind.TUPLE_EXPR, LPAREN, exprDocs(n), RPAREN);
            case LIST_EXPR -> list(n);
            case LIST_COMP -> listComp(n);
            case IF_EXPR -> ifExpr(n);
            case MATCH_EXPR -> matchExpr(n);
            case LAMBDA_EXPR -> lambda(n);
            case NEW_DATA_EXPR -> newData(n);
            case BLOCK_EXPR -> block(n);
            case UNREACHABLE_EXPR -> TokenDoc.node(n.kind(), concat(
                    TokenDoc.token(SyntaxKind.UNREACHABLE_KW, "unreachable"), GAP, expr(onlyExpr(n))));
            default -> throw new IllegalStateException("no case writes " + n.kind());
        };
    }

    /**
     * An argument list applied to the expression before it — every application, whatever is
     * applied. The callee is printed as the expression it is, so a qualified name reaches here as
     * the field read it was parsed as and no name is reassembled from the tokens under the node.
     *
     * <p>Printed on the line its callee ends on: an argument list that began the next line would be
     * a parenthesised expression rather than an application.
     */
    private TokenDoc apply(SyntaxNode n) {
        return TokenDoc.node(n.kind(), concat(expr(firstExprChild(n)), GAP, arguments(n)));
    }

    /** The bracketed argument list of a call or an application. */
    private TokenDoc arguments(SyntaxNode n) {
        List<SyntaxNode> args = n.child(SyntaxKind.ARG_LIST).map(this::exprChildren).orElse(List.of());
        SyntaxNode argList = n.child(SyntaxKind.ARG_LIST).orElse(null);
        if (args.isEmpty()) {
            List<Member> only = argList == null ? List.of() : withEndComments(argList, List.of());
            return delimited(SyntaxKind.ARG_LIST, LPAREN, only, RPAREN);
        }
        List<Member> argDocs = new ArrayList<>();
        for (SyntaxNode a : args) {
            argDocs.add(member(a, expr(a)));
        }
        return delimited(SyntaxKind.ARG_LIST, LPAREN, withEndComments(argList, argDocs), RPAREN);
    }

    private TokenDoc binary(SyntaxNode n) {
        List<Segment> segs = new ArrayList<>();
        TokenDoc head = collectChain(n, ladderLevel(operatorKind(n)), segs);
        return TokenDoc.node(n.kind(), chained(synthetic(head), segs));
    }

    /**
     * Flattens a run of operators the parser reads at one level of its precedence ladder, so that
     * what the source wrote as one run is laid out as one run: {@code a + b * c + d} breaks into
     * {@code a}, {@code + b * c} and {@code + d}, the three parts the {@code +} level has.
     *
     * <p>Only the left spine, and only within the level. The right operand of a left-associative
     * level is never that level's own operator unless the source parenthesised it, and a
     * parenthesised operand is a structure its author wrote — descending into either would show a
     * run the tree does not have.
     */
    private TokenDoc collectChain(SyntaxNode n, int level, List<Segment> segs) {
        List<SyntaxNode> ops = exprChildren(n);
        SyntaxNode left = ops.get(0);
        TokenDoc head;
        if (left.kind() == SyntaxKind.BINARY_EXPR && ladderLevel(operatorKind(left)) == level) {
            head = collectChain(left, level, segs);
        } else {
            head = concat(aboveOf(left), expr(left), afterOf(left));
        }
        SyntaxNode right = ops.get(1);
        segs.add(segment(token(operatorToken(n)), right, expr(right)));
        return head;
    }

    /**
     * Which rung of {@link CstParser}'s precedence ladder an operator is read on. Operators on one
     * rung are read by one loop and chain; the comparisons are read by a single test and never
     * chain, so their runs are one operator long and flattening them is a no-op.
     *
     * <p>An operator missing from here is refused rather than given a rung of its own: sharing one
     * would lay out a run the parser does not read as a run, which is the reading a reader takes
     * from the layout and cannot check.
     */
    private static int ladderLevel(SyntaxKind k) {
        return switch (k) {
            case OR -> 1;
            case AND -> 2;
            case EQ, NE, LT, LE, GT, GE -> 3;
            case PLUS, MINUS, PLUSPLUS -> 4;
            case STAR, SLASH -> 5;
            default -> throw new IllegalStateException("no precedence rung for " + k);
        };
    }

    private TokenDoc pipe(SyntaxNode n) {
        List<Segment> stages = new ArrayList<>();
        TokenDoc head = collectPipe(n, stages);
        return TokenDoc.node(n.kind(), chained(synthetic(head), stages));
    }

    /** Flattens a left-nested {@code |>} chain: returns the head doc and fills {@code stages} with each
     * right-hand stage in source order. */
    private TokenDoc collectPipe(SyntaxNode n, List<Segment> stages) {
        List<SyntaxNode> ops = exprChildren(n);
        SyntaxNode left = ops.get(0);
        SyntaxNode right = ops.get(1);
        TokenDoc head;
        if (left.kind() == SyntaxKind.PIPE_EXPR) {
            head = collectPipe(left, stages);
        } else {
            head = concat(aboveOf(left), expr(left), afterOf(left));
        }
        stages.add(segment(TokenDoc.token(SyntaxKind.VPIPE, "|>"), right, expr(right)));
        return head;
    }

    private TokenDoc list(SyntaxNode n) {
        return delimited(SyntaxKind.LIST_EXPR, LBRACKET, exprDocs(n), RBRACKET);
    }

    private TokenDoc listComp(SyntaxNode n) {
        List<Member> exprs = exprDocs(n);
        Member element = exprs.get(0);
        List<Member> guards = exprs.subList(1, exprs.size());
        // The `|` is the comprehension's and it is on the element's line, so it goes before the
        // comment that ends that line — as a comma does for a member of a list.
        return TokenDoc.node(n.kind(),
                group(concat(LBRACKET, GAP, element.doc(), GAP, PIPE, element.trailing(),
                        nest(INDENT, concat(SOFT_GAP, separated(guards))), SOFT_GAP, RBRACKET)));
    }

    private TokenDoc ifExpr(SyntaxNode n) {
        List<SyntaxNode> parts = exprChildren(n);
        TokenDoc departures = elseArms(n);
        return TokenDoc.node(n.kind(), group(concat(TokenDoc.token(SyntaxKind.IF_KW, "if"), GAP,
                expr(parts.get(0)), attemptBinder(n), GAP, TokenDoc.token(SyntaxKind.THEN_KW, "then"),
                nest(INDENT, concat(SOFT_GAP, expr(parts.get(1)))),
                SOFT_GAP, TokenDoc.token(SyntaxKind.ELSE_KW, "else"),
                departures != TokenDoc.NIL
                        ? departures
                        : nest(INDENT, concat(SOFT_GAP, expr(parts.get(2)))))));
    }

    /** An attempt's per-clause departures, one to a line under the {@code else}, or nothing where the
     * {@code else} took one expression. */
    private TokenDoc elseArms(SyntaxNode n) {
        var arms = n.child(SyntaxKind.ELSE_ARMS);
        if (arms.isEmpty()) {
            return TokenDoc.NIL;
        }
        List<TokenDoc> lines = new ArrayList<>();
        lines.add(afterToken(n.token(SyntaxKind.ELSE_KW)));
        for (SyntaxNode arm : childNodes(arms.get(), SyntaxKind.ELSE_ARM)) {
            lines.add(concat(HARD_GAP, aboveOf(arm), TokenDoc.node(arm.kind(),
                    concat(PIPE, GAP, ident(firstIdent(arm)), GAP, ARROW, GAP, expr(onlyExpr(arm)))),
                    afterOf(arm)));
        }
        lines.add(endOf(arms.get()));
        return TokenDoc.node(arms.get().kind(), nest(INDENT, concat(lines)));
    }

    /** The {@code as x} of an attempted construction, or nothing where none was written. It sits
     * between the construction and the {@code then}/{@code else} that follows it. */
    private TokenDoc attemptBinder(SyntaxNode n) {
        boolean afterAs = false;
        for (SyntaxElement e : meaningful(n)) {
            if (!(e instanceof SyntaxToken t)) continue;
            if (t.kind() == SyntaxKind.AS_KW) {
                afterAs = true;
            } else if (afterAs && t.kind() == SyntaxKind.IDENT) {
                return concat(GAP, TokenDoc.token(SyntaxKind.AS_KW, "as"), GAP, token(t));
            }
        }
        return TokenDoc.NIL;
    }

    private TokenDoc matchExpr(SyntaxNode n) {
        SyntaxNode scrutinee = exprChildren(n).get(0);
        List<TokenDoc> cases = new ArrayList<>();
        for (SyntaxNode c : childNodes(n, SyntaxKind.MATCH_CASE)) {
            cases.add(concat(HARD_GAP, concat(aboveOf(c), matchCase(c)), afterOf(c)));
        }
        cases.add(endOf(n));
        return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.MATCH_KW, "match"), GAP, expr(scrutinee),
                GAP, TokenDoc.token(SyntaxKind.WITH_KW, "with"),
                afterToken(n.token(SyntaxKind.WITH_KW)), nest(INDENT, concat(cases))));
    }

    /** The brackets a construct is written between. One place knows which they are. */
    static boolean isOpeningBracket(SyntaxKind k) {
        return k == SyntaxKind.LPAREN || k == SyntaxKind.LBRACKET || k == SyntaxKind.LBRACE;
    }

    static boolean isClosingBracket(SyntaxKind k) {
        return k == SyntaxKind.RPAREN || k == SyntaxKind.RBRACKET || k == SyntaxKind.RBRACE;
    }

    /**
     * One arm. The grammar writes an arm's pattern as a run of tokens rather than as nodes, so this
     * is where those tokens are handed over; what goes between two of them is the rule's answer for
     * the arm, the same way it is for every other construct. It used to be the one place the
     * formatter joined two tokens itself, and it wrote `Some ( x )` where the `let` opening the same
     * value writes `Some(x)`.
     */
    private TokenDoc matchCase(SyntaxNode n) {
        List<TokenDoc> pattern = new ArrayList<>();
        SyntaxNode body = null;
        SyntaxToken patternEnd = null;
        boolean afterArrow = false;
        for (SyntaxElement e : meaningful(n)) {
            if (afterArrow) {
                body = (SyntaxNode) e;
                break;
            }
            if (e instanceof SyntaxToken t) {
                if (t.kind() == SyntaxKind.ARROW) {
                    afterArrow = true;
                    continue;
                }
                if (patternEnd != null) {
                    pattern.add(GAP);
                }
                pattern.add(TokenDoc.token(t.kind(), t.text()));
                patternEnd = t;
            }
        }
        TokenDoc written = concat(pattern);
        return concat(PIPE, GAP, TokenDoc.node(n.kind(), chained(patternEnd == null
                        ? synthetic(written) : head(patternEnd, written),
                List.of(segment(ARROW, body, expr(body))))));
    }

    private TokenDoc lambda(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isPatternNode(c.kind())) {
                params.add(member(c, pattern(c)));
            }
        }
        // `x -> e` keeps its bare parameter; anything parenthesised was written that way
        TokenDoc paramsDoc = n.token(SyntaxKind.LPAREN).isPresent()
                ? delimited(SyntaxKind.LAMBDA_EXPR, LPAREN, withEndComments(n, params), RPAREN)
                : concat(params.get(0).doc(), params.get(0).trailing());
        return TokenDoc.node(n.kind(), concat(paramsDoc, GAP, ARROW, GAP, expr(lastExprChild(n))));
    }

    private TokenDoc newData(SyntaxNode n) {
        String typeName = firstIdent(n);
        List<Member> members = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            TokenDoc member;
            if (c.kind() == SyntaxKind.SPREAD_MEMBER) {
                // `...c` or `...c.address`
                member = TokenDoc.node(c.kind(), concat(
                        TokenDoc.token(SyntaxKind.SPREAD, "..."), GAP,
                        dottedName(idents(c))));
            } else if (c.kind() == SyntaxKind.FIELD_INIT) {
                var value = firstExprChildOpt(c);
                member = TokenDoc.node(c.kind(),
                        value.map(v -> concat(ident(firstIdent(c)), GAP, ASSIGN, GAP, expr(v)))
                                .orElse(ident(firstIdent(c))));   // shorthand `field`
            } else {
                continue;
            }
            // A member's leading comments come before it, each on its own line. The HARD_GAP forces
            // the enclosing group to break, which is what a literal with a comment in it wants
            // anyway: a `//` on a line the group had collapsed would swallow the rest of it.
            members.add(member(c, member));
        }
        return TokenDoc.node(n.kind(), concat(ident(typeName), GAP,
                delimited(SyntaxKind.NEW_DATA_EXPR, LBRACE, withEndComments(n, members), RBRACE)));
    }

    private TokenDoc block(SyntaxNode n) {
        List<TokenDoc> lines = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            // A statement inside a block carries its leading comments the same way a top-level item
            // does. Walking only the child nodes dropped them, so a comment explaining a step was
            // lost on the first format.
            TokenDoc lead = aboveOf(c);
            TokenDoc d = switch (c.kind()) {
                case LET_STMT -> TokenDoc.node(c.kind(), concat(TokenDoc.token(SyntaxKind.LET_KW, "let"), GAP, ident(firstIdent(c)),
                        writtenType(c), GAP, ASSIGN, GAP, expr(onlyExpr(c))));
                case LET_DESTRUCTURE -> TokenDoc.node(c.kind(), concat(TokenDoc.token(SyntaxKind.LET_KW, "let"), GAP,
                        pattern(patternChild(c)), GAP, ASSIGN, GAP, expr(onlyExpr(c))));
                case GUARD_STMT -> guardStmt(c);
                default -> expr(c);   // the result expression
            };
            lines.add(concat(HARD_GAP, lead, d, afterOf(c)));
        }
        lines.add(endOf(n));
        return TokenDoc.node(n.kind(), concat(LBRACE, afterToken(n.token(SyntaxKind.LBRACE)),
                nest(INDENT, concat(lines)), HARD_GAP, RBRACE));
    }

    /** A binding pattern, written back as it was: a name, a tuple, a newtype opened by its
     * constructor, or a record's fields. */
    private TokenDoc pattern(SyntaxNode n) {
        switch (n.kind()) {
            case PATTERN_NAME -> {
                return ident(firstIdent(n));
            }
            case PATTERN_TUPLE -> {
                List<Member> elems = new ArrayList<>();
                for (SyntaxNode c : n.childNodes()) {
                    if (isPatternNode(c.kind())) {
                        elems.add(member(c, pattern(c)));
                    }
                }
                return delimited(SyntaxKind.PATTERN_TUPLE, LPAREN, withEndComments(n, elems), RPAREN);
            }
            case PATTERN_CTOR -> {
                return TokenDoc.node(n.kind(), concat(qualifiedName(n), GAP, LPAREN, GAP,
                        pattern(patternChild(n)), GAP, RPAREN));
            }
            case PATTERN_RECORD -> {
                List<Member> fields = new ArrayList<>();
                for (SyntaxNode f : n.childNodes()) {
                    if (f.kind() != SyntaxKind.PATTERN_FIELD) {
                        continue;
                    }
                    List<SyntaxToken> names = idents(f);
                    fields.add(member(f, TokenDoc.node(f.kind(), names.size() > 1
                            ? concat(token(names.get(0)), GAP, ASSIGN, GAP, token(names.get(1)))
                            : token(names.get(0)))));
                }
                return delimited(SyntaxKind.PATTERN_RECORD, LBRACE, withEndComments(n, fields), RBRACE);
            }
            default -> {
                return ident(firstIdent(n));
            }
        }
    }

    private static boolean isPatternNode(SyntaxKind k) {
        return k == SyntaxKind.PATTERN_NAME || k == SyntaxKind.PATTERN_TUPLE
                || k == SyntaxKind.PATTERN_CTOR || k == SyntaxKind.PATTERN_RECORD;
    }

    private SyntaxNode patternChild(SyntaxNode n) {
        SyntaxNode c = optionalPatternChild(n);
        if (c == null) {
            throw new IllegalStateException("no pattern in " + n.kind());
        }
        return c;
    }

    private SyntaxNode optionalPatternChild(SyntaxNode n) {
        for (SyntaxNode c : n.childNodes()) {
            if (isPatternNode(c.kind())) {
                return c;
            }
        }
        return null;
    }

    private TokenDoc guardStmt(SyntaxNode n) {
        List<SyntaxNode> exprs = exprChildren(n);
        TokenDoc departures = elseArms(n);
        if (departures != TokenDoc.NIL) {
            return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.GUARD_KW, "guard"), GAP, expr(exprs.get(0)),
                    attemptBinder(n), GAP, TokenDoc.token(SyntaxKind.ELSE_KW, "else"), departures));
        }
        return TokenDoc.node(n.kind(), concat(TokenDoc.token(SyntaxKind.GUARD_KW, "guard"), GAP, expr(exprs.get(0)),
                attemptBinder(n), GAP, TokenDoc.token(SyntaxKind.ELSE_KW, "else"), GAP, expr(exprs.get(1))));
    }

    // --- comments ---
    //
    // Where a comment goes is decided once, for the file, and in two steps. What it was written
    // about is read off the token stream: a comment with a newline between it and the code before it
    // was written above the line that follows, and one without was written at the end of the line
    // before. That is a fact about the source and it is in the tree, since whitespace is kept.
    //
    // Where it is written back is a second question, and the answer is not always the construct it
    // was written about. Only a construct the layout gives a line of its own can carry a comment: put
    // anywhere else, the rest of that line would be written inside it, which changes what the code
    // says rather than how it reads. So the anchor moves up to the nearest construct that has a
    // line, and a comment written after the condition of an `if` is written at the end of the
    // declaration that holds it. It travels further than it was written; the alternative is dropping
    // it.

    /** Where the comments of a file go, decided before any of it is written. */
    private record Attachments(
            /** Above the line the node opens. */
            Map<SyntaxNode, List<SyntaxToken>> above,
            /** At the end of the line the node ends. */
            Map<SyntaxNode, List<SyntaxToken>> after,
            /** Inside the node, under its last member and before it closes. */
            Map<SyntaxNode, List<SyntaxToken>> atEnd,
            /** Against a bare token rather than a node — a sum's cases, which are identifiers.
             * Keyed by where the identifier starts, since a token has no identity of its own. */
            Map<Integer, List<SyntaxToken>> aboveCase,
            Map<Integer, List<SyntaxToken>> afterCase) {

        static Attachments empty() {
            return new Attachments(new IdentityHashMap<>(), new IdentityHashMap<>(),
                    new IdentityHashMap<>(), new java.util.HashMap<>(), new java.util.HashMap<>());
        }
    }

    /**
     * Every comment of {@code file}, against where it will be written. One pass over the tokens: a
     * comment is read as written above the code that follows it or at the end of the code before it,
     * and then given to whichever construct has the line that code is on.
     */
    private static Attachments attach(SyntaxNode file) {
        Attachments out = Attachments.empty();
        List<SyntaxToken> all = tokens(file);
        List<SyntaxToken> code = new ArrayList<>();   // the tokens that were not trivia
        boolean lineEnded = true;                     // nothing precedes the first token of a file
        for (int i = 0; i < all.size(); i++) {
            SyntaxToken t = all.get(i);
            if (t.kind() == SyntaxKind.WHITESPACE) {
                lineEnded |= t.text().indexOf('\n') >= 0;
            } else if (t.kind() == SyntaxKind.LINE_COMMENT) {
                if (lineEnded) {
                    above(out, nextCode(all, i), t, file);
                } else {
                    after(out, lastCode(code), t);
                }
                lineEnded = true;                     // a line comment runs to the end of its line
            } else {
                code.add(t);
                lineEnded = false;
            }
        }
        return out;
    }

    /**
     * What separates one member of a construct from the next. It belongs to the construct rather
     * than to either member, so it is not what a comment was written about in either direction: a
     * comment before a {@code |} was written about the case after it, and one after a {@code ,} about
     * the member the comma closed.
     */
    private static boolean separates(SyntaxToken t) {
        return switch (t.kind()) {
            case COMMA, PIPE, PIPEFWD, VPIPE -> true;
            // An arrow joins two parts of a chain only where a chain is what the layout writes. A
            // function type and a lambda are written as one line with an arrow in it, and a comment
            // before that arrow has no part after it to be about — reading it as a connector there
            // moved the comment on the first formatting and moved it again on the second.
            case ARROW, COLON -> switch (t.parent().kind()) {
                case EXAMPLE_ROW, FAKE_ROW, MATCH_CASE -> true;
                default -> false;
            };
            default -> isBinaryOperator(t.kind());
        };
    }

    /** What opens a construct. It is the construct's too, so a comment written above it was written
     * above the first member rather than above the bracket — which is also what keeps the answer
     * the same on a second formatting, when the bracket has moved onto the member's line. */
    private static boolean opens(SyntaxToken t) {
        return isOpeningBracket(t.kind());
    }

    /** The code the comment at {@code i} was written above, or null where the file ends first. */
    private static SyntaxToken nextCode(List<SyntaxToken> all, int i) {
        for (int j = i + 1; j < all.size(); j++) {
            SyntaxToken t = all.get(j);
            // what closes a construct is asked about before what separates its members, because a
            // type's `>` is both: it is the angle bracket here and the comparison everywhere else
            if (t.isTrivia() || (separates(t) && !closes(t))) {
                continue;
            }
            return t.kind() == SyntaxKind.EOF ? null : t;
        }
        return null;
    }

    /** The code a comment was written after. */
    private static SyntaxToken lastCode(List<SyntaxToken> code) {
        for (int i = code.size() - 1; i >= 0; i--) {
            if (!separates(code.get(i)) || closes(code.get(i))) {
                return code.get(i);
            }
        }
        return null;
    }

    /**
     * What a comment written above {@code next} was written about: the outermost construct that
     * begins there. This is what the comment describes, and it is decided without asking whether
     * that construct has anywhere to put it — that is the next question, and answering the two
     * together is what turned a comment about a case into a comment about the declaration.
     */
    private static void above(Attachments out, SyntaxToken next, SyntaxToken comment, SyntaxNode file) {
        SyntaxNode begins = next == null ? null : beginningAt(next);
        // What opens a construct is the construct's, and it shares a line with the first member —
        // unless a member begins at that bracket itself, as a `fake` row does at its `(`, in which
        // case the comment is above the member and not above what the member opens with.
        boolean opensSomethingElse = begins != null && begins.parent() != null
                && !takesALineOf(begins.parent().kind(), begins.kind());
        if (next != null && opens(next) && opensSomethingElse) {
            SyntaxElement first = firstMemberOf(next.parent());
            if (first instanceof SyntaxNode node) {
                place(out, node, comment, true);
                return;
            }
            if (first instanceof SyntaxToken token) {
                out.aboveCase().computeIfAbsent(nameStart(token), _ -> new ArrayList<>()).add(comment);
                return;
            }
        }
        if (next == null) {
            add(out.atEnd(), file, comment);          // nothing follows: it closes the file
        } else if (isBareMember(next)) {
            // A clause keyword opens the line its first name is on, the way a bracket does, so a
            // comment above that name is above the clause rather than between the two.
            SyntaxElement first = firstMemberOf(next.parent());
            boolean opensTheClause = first instanceof SyntaxToken t && t.start() == nameStart(next)
                    && (next.parent().kind() == SyntaxKind.CONSTRUCTS_CLAUSE
                            || next.parent().kind() == SyntaxKind.DEPENDS_CLAUSE);
            if (opensTheClause) {
                place(out, next.parent(), comment, true);
            } else {
                out.aboveCase().computeIfAbsent(nameStart(next), _ -> new ArrayList<>()).add(comment);
            }
        } else if (closes(next)) {
            add(out.atEnd(), next.parent(), comment);
        } else {
            place(out, begins, comment, true);
        }
    }

    /** What a comment written after {@code code} was written about: the outermost construct that
     * ends there. */
    private static void after(Attachments out, SyntaxToken code, SyntaxToken comment) {
        if (code == null) {
            return;                                   // a comment with no code before it is above
        }
        // A bare member is only its own line's owner while something follows it. The last case of a
        // sum ends where the declaration does, and what ends on that line is the declaration.
        // Measured from the end of the whole name, not from the identifier the comment happens to
        // follow: a comment inside `other.mod.Thing` and one after it are about the same member, and
        // the last member of a run ends where the run does, which is the run's line and not its own.
        if (isBareMember(code) && nameEnd(code) != code.parent().end()) {
            out.afterCase().computeIfAbsent(nameEnd(code), _ -> new ArrayList<>()).add(comment);
            return;
        }
        if (isChainHead(code)) {
            out.afterCase().computeIfAbsent(code.end(), _ -> new ArrayList<>()).add(comment);
            return;
        }
        // Of the constructs ending where the comment is, the outermost one the layout gives a line
        // to. Outermost because `data D = A | B // c` is about the declaration and not about `B`;
        // only among those that have a line, because a `with` binding has one even though the row
        // it is in goes on to its expected value — the comment is itself what ends that line.
        SyntaxNode slot = slotEndingAt(code);
        if (slot == null) {
            // Nothing ends here, so the comment was written in the middle of a construct: it ends
            // the line that construct is on, which is where the same comment written after that
            // construct's last token would go. Reading the two the same way is what makes the
            // answer survive a second formatting.
            slot = slotOf(endingAt(code));
        }
        if (slot == null) {
            return;
        }
        // A pipeline's declared output is written after its last stage and on that stage's line, so
        // the stage is not what ends the line: what ends it is the declaration.
        boolean moreOfTheLineFollows = slot.parent() != null
                && slot.parent().kind() == SyntaxKind.PIPE_BEHAVIOR
                && slot.end() != slot.parent().end();
        if ((slot.end() != code.end() || moreOfTheLineFollows) && !endsAWrittenLine(code)) {
            SyntaxToken last = lastCodeTokenOf(moreOfTheLineFollows ? slot.parent() : slot);
            if (last != null && last.end() != code.end()) {
                SyntaxNode wider = slotOf(endingAt(last));
                if (wider != null) {
                    slot = wider;
                }
            }
        }
        if (slot.end() != code.end() && endsAWrittenLine(code)) {
            out.afterCase().computeIfAbsent(code.end(), _ -> new ArrayList<>()).add(comment);
        } else {
            add(out.after(), slot, comment);
        }
    }

    /**
     * Files {@code comment} against {@code owner}, or against the nearest construct above it that
     * the layout gives a line of its own. A construct with no line of its own has nowhere to put a
     * comment: written there, the rest of that line would be written inside it. So the comment
     * travels — a comment after the condition of an {@code if} is written at the end of the
     * declaration that holds the {@code if} — and how far it travels is a fact about the layout
     * rather than about what the comment was written about.
     */
    private static void place(Attachments out, SyntaxNode owner, SyntaxToken comment, boolean above) {
        SyntaxNode slot = slotOf(owner, above);
        if (slot != null) {
            add(above ? out.above() : out.after(), slot, comment);
        }
    }

    /**
     * Whether the layout always ends a line at {@code t}. These are the tokens a construct written
     * over several lines opens with — the {@code =} of a product block, the {@code with} of a match,
     * the {@code {} of a block — where the line a comment ends is the construct's first and not its
     * last. Whether a bracketed construct breaks depends on its width, so its brackets are not here:
     * a comment there goes to the line the whole construct ends.
     */
    private static boolean endsAWrittenLine(SyntaxToken t) {
        SyntaxNode parent = t.parent();
        return switch (t.kind()) {
            case ASSIGN -> parent.kind() == SyntaxKind.DATA_DEF
                    && parent.child(SyntaxKind.PRODUCT_BODY).isPresent();
            case WITH_KW -> parent.kind() == SyntaxKind.MATCH_EXPR;
            case LBRACE -> parent.kind() == SyntaxKind.BLOCK_EXPR;
            case ELSE_KW -> parent.child(SyntaxKind.ELSE_ARMS).isPresent();
            case IDENT -> (parent.kind() == SyntaxKind.EXAMPLE_DEF
                        || parent.kind() == SyntaxKind.FAKE_DEF)
                    // the target, not the `example` that opens the line with it
                    && lastIdentOf(parent) != null && lastIdentOf(parent).end() == t.end();
            default -> false;
        };
    }

    /** {@code n}'s first child node, whether or not the layout gives it a line. */
    private static SyntaxNode firstChildOf(SyntaxNode n) {
        for (SyntaxNode c : n.childNodes()) {
            return c;
        }
        return null;
    }

    private static SyntaxToken lastCodeTokenOf(SyntaxNode n) {
        SyntaxToken last = null;
        for (SyntaxToken t : tokens(n)) {
            if (!t.isTrivia()) {
                last = t;
            }
        }
        return last;
    }

    private static SyntaxToken lastIdentOf(SyntaxNode n) {
        SyntaxToken last = null;
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                last = t;
            }
        }
        return last;
    }

    /** The outermost construct ending at {@code code} that the layout gives a line of its own, or
     * nothing where none of them has one. */
    private static SyntaxNode slotEndingAt(SyntaxToken code) {
        SyntaxNode best = null;
        for (SyntaxNode c = code.parent();
                c != null && c.parent() != null && c.end() == code.end();
                c = c.parent()) {
            // The last part of a run has a line only while the run is inside another one. The last
            // part of the outermost run ends where the run does, and what the run is inside goes on
            // writing that line — a condition's `then`, a call's `)`.
            boolean endsTheOutermostRun = isSpine(c.parent()) && c.end() == c.parent().end()
                    && !isSpine(c.parent().parent());
            if (takesALineOf(c.parent().kind(), c.kind()) && !endsTheOutermostRun) {
                best = c;
            }
        }
        return best;
    }

    /** The construct that owns the line {@code owner} is written on. */
    /**
     * Whether {@code child} opens a line of {@code parent} as well as ending one. A construct the
     * parent writes a prefix in front of — a newtype's body after the {@code =}, a signature's
     * return type after the {@code ->} — ends the line it is on and does not begin it, since the
     * prefix is already there. A comment above it goes above the line the prefix opens, which
     * belongs to whatever wrote the prefix.
     */
    private static boolean opensALine(SyntaxNode c) {
        if (!takesALineOf(c.parent().kind(), c.kind())) {
            return false;
        }
        SyntaxKind parent = c.parent().kind();
        if (parent == SyntaxKind.DATA_DEF && c.kind() == SyntaxKind.NEWTYPE_BODY) {
            return false;
        }
        if (parent == SyntaxKind.BEHAVIOR_SIG && c.kind() == SyntaxKind.RET_TYPE) {
            return false;
        }
        // The first of a run is written after whatever opens it and the rest after a break, so only
        // the rest have a line of their own to be written above. The head of a chain is the first of
        // its run, and so is the first binding of a `with`.
        return !isFirstOfItsRun(c);
    }

    /** Whether {@code c} is the first member of a run the layout opens with text of its own rather
     * than with a break — the left of a chain, an example row's input where no description precedes
     * it, the first binding after a {@code with}. */
    private static boolean isFirstOfItsRun(SyntaxNode c) {
        SyntaxNode parent = c.parent();
        return switch (parent.kind()) {
            // the left of a run, which is the run's own left where the run nests: `a |> b |> c` is
            // read as `(a |> b) |> c`, and the part that opens the line is `a`
            case BINARY_EXPR, PIPE_EXPR, RET_TYPE, WITH_CLAUSE, LIST_COMP -> firstChildOf(parent) == c;
            case EXAMPLE_ROW -> c.kind() == SyntaxKind.ARG_LIST
                    && parent.token(SyntaxKind.STRING_LIT).isEmpty();
            case FAKE_ROW -> c.kind() == SyntaxKind.ARG_LIST;
            default -> false;
        };
    }

    private static SyntaxNode slotOf(SyntaxNode owner) {
        return slotOf(owner, false);
    }

    private static SyntaxNode slotOf(SyntaxNode owner, boolean above) {
        SyntaxNode from = owner;
        // A run the layout flattens is written as segments, and a part of the spine ends where its
        // own segment does rather than where the whole run does. Only inside the run, though: the
        // last segment of the outermost run is followed by whatever the construct holding it writes
        // — a `then`, a closing bracket — and a comment there would have that written inside it.
        while (isSpine(from) && from.parent() != null && from.parent().kind() == from.kind()) {
            from = lastSegmentOf(from);
        }
        for (SyntaxNode c = from; c != null && c.parent() != null; c = c.parent()) {
            if (above ? opensALine(c) : takesALineOf(c.parent().kind(), c.kind())) {
                return c;
            }
        }
        return null;
    }

    /** Whether {@code n} is a run the layout writes as one chain of segments rather than as the
     * nesting the parser read. */
    private static boolean isSpine(SyntaxNode n) {
        return n.kind() == SyntaxKind.PIPE_EXPR || n.kind() == SyntaxKind.BINARY_EXPR;
    }

    /** The part of a flattened run that is written last — the segment whose line the run ends on. */
    private static SyntaxNode lastSegmentOf(SyntaxNode n) {
        List<SyntaxNode> parts = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isExprKind(c.kind())) {
                parts.add(c);
            }
        }
        return parts.get(parts.size() - 1);
    }

    /** The outermost construct beginning at {@code t}. */
    private static SyntaxNode beginningAt(SyntaxToken t) {
        SyntaxNode node = t.parent();
        while (node.parent() != null && node.parent().parent() != null
                && firstCodeOffset(node.parent()) == t.start()) {
            node = node.parent();
        }
        return node;
    }

    /** The outermost construct ending at {@code t}. */
    private static SyntaxNode endingAt(SyntaxToken t) {
        SyntaxNode node = t.parent();
        while (node.parent() != null && node.parent().parent() != null
                && node.parent().end() == t.end()) {
            node = node.parent();
        }
        return node;
    }

    /** Where {@code n}'s own text begins, past whatever trivia the parser put in front of it. */
    private static int firstCodeOffset(SyntaxNode n) {
        for (SyntaxToken t : tokens(n)) {
            if (!t.isTrivia()) {
                return t.start();
            }
        }
        return n.start();
    }

    /**
     * A qualified name is one member written as several identifiers, so a comment anywhere in it is
     * about the whole name. These answer where that name begins and ends, so the two ends of the
     * run agree on which member they are, however deep into it the comment was written.
     */
    private static int nameStart(SyntaxToken ident) {
        SyntaxToken at = ident;
        for (SyntaxToken before = previousOfName(at); before != null; before = previousOfName(at)) {
            at = before;
        }
        return at.start();
    }

    private static int nameEnd(SyntaxToken ident) {
        SyntaxToken at = ident;
        for (SyntaxToken after = nextOfName(at); after != null; after = nextOfName(at)) {
            at = after;
        }
        return at.end();
    }

    private static SyntaxToken previousOfName(SyntaxToken ident) {
        List<SyntaxToken> siblings = codeTokensOf(ident.parent());
        int i = indexOf(siblings, ident);
        return i >= 2 && siblings.get(i - 1).kind() == SyntaxKind.DOT ? siblings.get(i - 2) : null;
    }

    private static SyntaxToken nextOfName(SyntaxToken ident) {
        List<SyntaxToken> siblings = codeTokensOf(ident.parent());
        int i = indexOf(siblings, ident);
        return i >= 0 && i + 2 < siblings.size() && siblings.get(i + 1).kind() == SyntaxKind.DOT
                ? siblings.get(i + 2) : null;
    }

    private static List<SyntaxToken> codeTokensOf(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia()) {
                out.add(t);
            }
        }
        return out;
    }

    private static int indexOf(List<SyntaxToken> tokens, SyntaxToken t) {
        for (int i = 0; i < tokens.size(); i++) {
            if (tokens.get(i).start() == t.start()) {
                return i;
            }
        }
        return -1;
    }

    private static void add(Map<SyntaxNode, List<SyntaxToken>> to, SyntaxNode key, SyntaxToken c) {
        to.computeIfAbsent(key, _ -> new ArrayList<>()).add(c);
    }

    /** The first of {@code container}'s members, which is what shares the line its opener starts.
     * Nothing where it has no members: an empty construct's brackets open and close one line. */
    private static SyntaxElement firstMemberOf(SyntaxNode container) {
        for (SyntaxElement e : container.children()) {
            if (e instanceof SyntaxNode c && takesALineOf(container.kind(), c.kind())) {
                return c;
            }
            if (e instanceof SyntaxToken t && isBareMember(t)) {
                return t;
            }
        }
        return null;
    }

    /**
     * A member the grammar writes as a bare identifier rather than as a node — a sum's cases, the
     * names an import or a {@code constructs} clause lists. It has no node to be named by, so it is
     * named by where its identifier is.
     *
     * <p>The identifier a {@code depends on} clause opens with is the {@code on}, which is the
     * keyword and not a name.
     */
    private static boolean isBareMember(SyntaxToken t) {
        if (t.kind() != SyntaxKind.IDENT) {
            return false;
        }
        SyntaxNode parent = t.parent();
        return switch (parent.kind()) {
            case SUM_BODY, NAME_LIST, CONSTRUCTS_CLAUSE -> true;
            case DEPENDS_CLAUSE -> !t.equals(firstIdentToken(parent));
            default -> false;
        };
    }

    /** A token the head of a chain is written from — a match arm's pattern, an example row's
     * description. Like a sum's cases these are tokens rather than nodes, so they are named by where
     * they are; unlike them they open a chain rather than being one of its parts. */
    private static boolean isChainHead(SyntaxToken t) {
        return switch (t.parent().kind()) {
            case EXAMPLE_ROW -> t.kind() == SyntaxKind.STRING_LIT;
            case MATCH_CASE -> t.kind() != SyntaxKind.ARROW && followedByArrow(t);
            default -> false;
        };
    }

    private static boolean followedByArrow(SyntaxToken t) {
        boolean after = false;
        for (SyntaxElement e : t.parent().children()) {
            if (!(e instanceof SyntaxToken s) || s.isTrivia()) {
                continue;
            }
            if (after) {
                return s.kind() == SyntaxKind.ARROW;
            }
            after = s.start() == t.start();
        }
        return false;
    }

    private static SyntaxToken firstIdentToken(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                return t;
            }
        }
        return null;
    }

    /** Whether {@code t} is what closes a construct whose members take a line each — the place a
     * comment written under the last member goes. */
    private static boolean closes(SyntaxToken t) {
        if (!holdsLines(t.parent().kind())) {
            return false;
        }
        // Usually a construct's members run to its own end. A function type and a parenthesised
        // lambda are written as one node whose members stop at a bracket in the middle of it —
        // `(Int, String) -> Bool` — and the layout writes that bracketed run as a construct of its
        // own, so what closes the run closes something even though it closes no node.
        boolean ends = t.end() == t.parent().end()
                || ((t.parent().kind() == SyntaxKind.FN_TYPE
                        || t.parent().kind() == SyntaxKind.LAMBDA_EXPR)
                    && t.kind() == SyntaxKind.RPAREN);
        return ends && switch (t.kind()) {
            case RBRACE, RPAREN, RBRACKET, GT -> true;
            default -> false;
        };
    }

    /**
     * The construct whose line {@code t} is on: the nearest one at or above it that the layout gives
     * a line of its own.
     */
    private static SyntaxNode hasALine(SyntaxToken t) {
        for (SyntaxNode c = t.parent(); c != null && c.parent() != null; c = c.parent()) {
            if (takesALineOf(c.parent().kind(), c.kind())) {
                return c;
            }
        }
        return null;
    }

    /** Whether a {@code child} of {@code parent} is written on a line of its own. */
    private static boolean takesALineOf(SyntaxKind parent, SyntaxKind child) {
        java.util.function.Predicate<SyntaxKind> children = linesOf(parent);
        return children != null && children.test(child);
    }

    /** Whether {@code parent} writes any of its children on lines of their own, so that what closes
     * it opens a line too. Read from the same table as {@link #takesALineOf}: a construct that holds
     * lines and a construct whose members can be written above are the same construct, and keeping
     * two lists of them is how a type argument came to have somewhere to put the comment under it
     * while nothing put one there. */
    private static boolean holdsLines(SyntaxKind parent) {
        return linesOf(parent) != null;
    }

    /**
     * Which children of {@code parent} are written on lines of their own, or null where none are.
     * These are the places a construct is asked for its comments; one added here without being asked
     * is what counting the comments consumed against the comments the tree holds is there to catch.
     */
    private static java.util.function.Predicate<SyntaxKind> linesOf(SyntaxKind parent) {
        return switch (parent) {
            case SOURCE_FILE -> Formatter::isTopLevel;
            case PRODUCT_BODY, NEW_DATA_EXPR ->
                    k -> k == SyntaxKind.FIELD || k == SyntaxKind.FIELD_INIT
                            || k == SyntaxKind.SPREAD_MEMBER;
            case MATCH_EXPR -> k -> k == SyntaxKind.MATCH_CASE;
            case MATCH_CASE -> Formatter::isExprKind;
            case EXAMPLE_ROW, FAKE_ROW -> k -> k == SyntaxKind.ARG_LIST || isExprKind(k);
            case EXAMPLE_DEF -> k -> k == SyntaxKind.EXAMPLE_ROW;
            case FAKE_DEF -> k -> k == SyntaxKind.FAKE_ROW;
            case EXPOSING_CLAUSE -> k -> k == SyntaxKind.EXPOSED_ENTRY;
            case PARAM_LIST -> k -> k == SyntaxKind.PARAM;
            case FN_PARAM_LIST -> k -> k == SyntaxKind.FN_PARAM;
            case WITH_CLAUSE -> k -> k == SyntaxKind.WITH_BINDING;
            case ELSE_ARMS -> k -> k == SyntaxKind.ELSE_ARM;
            case PIPE_BEHAVIOR -> k -> k == SyntaxKind.STAGE;
            case DATA_DEF -> k -> k == SyntaxKind.INVARIANT_CLAUSE
                    || k == SyntaxKind.NEWTYPE_BODY;
            case BEHAVIOR_SIG -> k -> k == SyntaxKind.CONSTRUCTS_CLAUSE
                    || k == SyntaxKind.DEPENDS_CLAUSE || k == SyntaxKind.RET_TYPE;
            case RET_TYPE, TYPE_ARGS, TUPLE_TYPE -> Formatter::isTypeNode;
            case FN_TYPE -> k -> k == SyntaxKind.RET_TYPE;
            case LAMBDA_EXPR, PATTERN_TUPLE -> Formatter::isPatternNode;
            case PATTERN_RECORD -> k -> k == SyntaxKind.PATTERN_FIELD;
            case BINARY_EXPR -> k -> isExprKind(k) && k != SyntaxKind.BINARY_EXPR;
            case BLOCK_EXPR -> _ -> true;
            case ARG_LIST, LIST_EXPR, TUPLE_EXPR, LIST_COMP -> Formatter::isExprKind;
            case PIPE_EXPR -> k -> isExprKind(k) && k != SyntaxKind.PIPE_EXPR;
            default -> null;
        };
    }

    // --- writing them back ---

    /** {@code run} as documents, each marked consumed as it is taken. A comment is taken once. */
    private List<TokenDoc> unwritten(List<SyntaxToken> run) {
        List<TokenDoc> out = new ArrayList<>();
        for (SyntaxToken c : run) {
            if (consumedComments.add(c.start())) {
                out.add(TokenDoc.comment(c.text().stripTrailing()));
            }
        }
        return out;
    }

    /** The comments written above {@code n}, each on its own line in front of it. The
     * {@link TokenDoc#HARD_GAP} after each forces the enclosing group to break: a {@code //} on a line the
     * group had collapsed would swallow everything after it. */
    private TokenDoc aboveOf(SyntaxNode n) {
        List<TokenDoc> parts = new ArrayList<>();
        for (TokenDoc c : unwritten(comments.above().getOrDefault(n, List.of()))) {
            parts.add(concat(c, HARD_GAP));
        }
        return concat(parts);
    }

    /** The comment written at the end of {@code n}'s line. */
    private TokenDoc afterOf(SyntaxNode n) {
        List<TokenDoc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.after().getOrDefault(n, List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(TokenDoc.trailing(c.text().stripTrailing()));
            }
        }
        return concat(parts);
    }

    /** The comments written inside {@code n} under its last member, each opening a line. */
    private TokenDoc endOf(SyntaxNode n) {
        List<TokenDoc> parts = new ArrayList<>();
        for (TokenDoc c : endLines(n)) {
            parts.add(concat(HARD_GAP, c));
        }
        return concat(parts);
    }

    private List<TokenDoc> endLines(SyntaxNode n) {
        return unwritten(comments.atEnd().getOrDefault(n, List.of()));
    }

    /** The comments written above a sum's case, which is an identifier and not a node. */
    private List<TokenDoc> aboveCase(SyntaxToken ident) {
        return unwritten(comments.aboveCase().getOrDefault(ident.start(), List.of()));
    }

    /** The comment written at the end of a sum case's line. */
    private TokenDoc afterCase(SyntaxToken ident) {
        List<TokenDoc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.afterCase().getOrDefault(ident.end(), List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(TokenDoc.trailing(c.text().stripTrailing()));
            }
        }
        return concat(parts);
    }

    /** The comment written at the end of the line {@code t} ends, where that is a line inside a
     * construct rather than the construct's own last line. */
    private TokenDoc afterToken(java.util.Optional<SyntaxToken> t) {
        return t.map(this::afterToken).orElse(TokenDoc.NIL);
    }

    private TokenDoc afterToken(SyntaxToken t, boolean present) {
        return present ? afterToken(t) : TokenDoc.NIL;
    }

    private TokenDoc afterToken(SyntaxToken t) {
        List<TokenDoc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.afterCase().getOrDefault(t.end(), List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(TokenDoc.trailing(c.text().stripTrailing()));
            }
        }
        return concat(parts);
    }

    /** A member the grammar wrote as an identifier: the same shape as one written as a node, held
     * against where the identifier is. */
    private Member tokenMember(SyntaxToken above, SyntaxToken end, TokenDoc d) {
        List<TokenDoc> lead = new ArrayList<>();
        for (TokenDoc c : unwritten(comments.aboveCase().getOrDefault(nameStart(above), List.of()))) {
            lead.add(concat(c, HARD_GAP));
        }
        List<TokenDoc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.afterCase().getOrDefault(nameEnd(end), List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(TokenDoc.trailing(c.text().stripTrailing()));
            }
        }
        return new Member(concat(concat(lead), d), concat(parts));
    }

    /** A member: what is written above its line, the member, and what ends that line — the last kept
     * apart because whatever the enclosing construct writes between this member and the next belongs
     * on this line, before the comment. */
    private Member member(SyntaxNode node, TokenDoc d) {
        return new Member(concat(aboveOf(node), d), afterOf(node));
    }

    /** {@code members} of {@code parent} with the comments written under the last of them. A
     * construct with no members at all still has somewhere to put them: between its brackets, which
     * is where they were written. */
    private List<Member> withEndComments(SyntaxNode parent, List<Member> members) {
        List<TokenDoc> end = endLines(parent);
        if (end.isEmpty()) {
            return members;
        }
        List<TokenDoc> lines = new ArrayList<>();
        for (TokenDoc c : end) {
            lines.add(concat(HARD_GAP, c));
        }
        List<Member> out = new ArrayList<>(members);
        if (out.isEmpty()) {
            // a construct with no members still has between its brackets, which is where they were
            // written; the comments stand where a member would have, so they bring no line of their
            // own — the brackets already open and close one
            out.add(new Member(concat(TokenDoc.MUST_BREAK, TokenDoc.join(HARD_GAP, end)), TokenDoc.NIL));
            return out;
        }
        Member last = out.get(out.size() - 1);
        out.set(out.size() - 1,
                new Member(concat(last.doc(), last.trailing(), concat(lines)), TokenDoc.NIL));
        return out;
    }

    /** Every token of {@code n}'s subtree, in document order. */
    private static List<SyntaxToken> tokens(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                out.addAll(tokens(c));
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
        return out;
    }


    // --- CST navigation ---

    private TokenDoc qualifiedName(SyntaxNode n) {
        return TokenDoc.node(n.kind(), dottedName(idents(n)));
    }

    /**
     * A name written through the module or the alias that declares it: its identifiers, and the
     * dots the canonical form writes between them. What goes at each of those boundaries is the
     * rule's to say, which is why the name is handed over as its tokens rather than assembled into
     * one — assembling it is deciding, and a name is one of the places the same decision used to be
     * written out again.
     */
    /** A token of the source, written back as itself. */
    private static TokenDoc token(SyntaxToken t) {
        return TokenDoc.token(t.kind(), t.text());
    }

    /** An identifier the canonical form writes. */
    private static TokenDoc ident(String text) {
        return TokenDoc.token(SyntaxKind.IDENT, text);
    }

    private static TokenDoc dottedName(List<SyntaxToken> idents) {
        List<TokenDoc> parts = new ArrayList<>();
        for (SyntaxToken t : idents) {
            if (!parts.isEmpty()) {
                parts.add(GAP);
                parts.add(DOT);
                parts.add(GAP);
            }
            parts.add(TokenDoc.token(t.kind(), t.text()));
        }
        return concat(parts);
    }

    private List<Member> exprDocs(SyntaxNode n) {
        List<Member> out = new ArrayList<>();
        for (SyntaxNode c : exprChildren(n)) {
            out.add(member(c, expr(c)));
        }
        return withEndComments(n, out);
    }

    private List<SyntaxNode> exprChildren(SyntaxNode n) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isExprKind(c.kind())) {
                out.add(c);
            }
        }
        return out;
    }

    private SyntaxNode firstExprChild(SyntaxNode n) {
        return exprChildren(n).get(0);
    }

    private Optional<SyntaxNode> firstExprChildOpt(SyntaxNode n) {
        List<SyntaxNode> c = exprChildren(n);
        return c.isEmpty() ? Optional.empty() : Optional.of(c.get(0));
    }

    private SyntaxNode lastExprChild(SyntaxNode n) {
        List<SyntaxNode> c = exprChildren(n);
        return c.get(c.size() - 1);
    }

    private SyntaxNode onlyExpr(SyntaxNode n) {
        return firstExprChild(n);
    }

    private static boolean isExprKind(SyntaxKind k) {
        return switch (k) {
            case LITERAL_EXPR, VAR_EXPR, FIELD_ACCESS, APPLY_EXPR, BINARY_EXPR,
                 UNARY_EXPR, PIPE_EXPR, PAREN_EXPR, TUPLE_EXPR, LIST_EXPR, LIST_COMP, IF_EXPR,
                 MATCH_EXPR, LAMBDA_EXPR, FIELD_GETTER, NEW_DATA_EXPR, BLOCK_EXPR,
                 UNREACHABLE_EXPR -> true;
            default -> false;
        };
    }

    private List<SyntaxNode> childNodes(SyntaxNode n, SyntaxKind kind) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (c.kind() == kind) {
                out.add(c);
            }
        }
        return out;
    }

    private List<SyntaxToken> idents(SyntaxNode n) {
        List<SyntaxToken> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                out.add(t);
            }
        }
        return out;
    }

    private String firstIdent(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                return t.text();
            }
        }
        throw new IllegalStateException("no identifier in " + n.kind());
    }

    private String lastIdent(SyntaxNode n) {
        String last = null;
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                last = t.text();
            }
        }
        return last;
    }

    private String operatorText(SyntaxNode n) {
        return operatorToken(n).text();
    }

    private SyntaxKind operatorKind(SyntaxNode n) {
        return operatorToken(n).kind();
    }

    private SyntaxToken operatorToken(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia() && isBinaryOperator(t.kind())) {
                return t;
            }
        }
        throw new IllegalStateException("no operator in " + n.kind());
    }

    private static boolean isBinaryOperator(SyntaxKind k) {
        return switch (k) {
            case EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS, STAR, SLASH, PLUSPLUS -> true;
            default -> false;
        };
    }

    private SyntaxNode typeChild(SyntaxNode n) {
        for (SyntaxNode c : n.childNodes()) {
            if (isTypeNode(c.kind())) {
                return c;
            }
        }
        throw new IllegalStateException("no type in " + n.kind());
    }

    private List<SyntaxElement> meaningful(SyntaxNode n) {
        List<SyntaxElement> out = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode || (e instanceof SyntaxToken t && !t.isTrivia())) {
                out.add(e);
            }
        }
        return out;
    }

    private SyntaxToken firstMeaningfulToken(SyntaxNode n) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia()) {
                return t;
            }
        }
        throw new IllegalStateException("no token in " + n.kind());
    }
}
