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

import static souther.compiler.fmt.Doc.HARDLINE;
import static souther.compiler.fmt.Doc.LINE;
import static souther.compiler.fmt.Doc.SOFTLINE;
import static souther.compiler.fmt.Doc.concat;
import static souther.compiler.fmt.Doc.group;
import static souther.compiler.fmt.Doc.nest;
import static souther.compiler.fmt.Doc.text;

/**
 * A single-canonical-form (gofmt-style) formatter over the concrete syntax tree. It re-derives the
 * layout from the tree's structure and a fixed style — a product type as a leading-comma block, a
 * record literal as a trailing-comma {@code Type { ... }}, a {@code |>} pipeline one stage per line —
 * choosing inline or broken by whether the construct fits {@link #WIDTH} columns. Full-line comments
 * are kept above the construct they precede; blank lines between top-level items collapse to one.
 */
public final class Formatter {

    private static final int INDENT = 4;

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
            Doc doc = formatter.file(file);
            List<SyntaxToken> missing = unconsumed(file, formatter.consumedComments);
            if (!missing.isEmpty()) {
                throw new IllegalStateException(
                        missing.size() + " comment(s) in this source reached no construct and would"
                                + " have been dropped; the first is at offset "
                                + missing.get(0).start() + ": "
                                + missing.get(0).text().stripTrailing());
            }
            return doc.render(WIDTH);
        } catch (StackOverflowError _) {
            throw tooDeep();
        }
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
    private record Member(Doc doc, Doc trailing) {}

    /** Members that carry no comment of their own. */
    private static List<Member> plain(List<Doc> docs) {
        List<Member> out = new ArrayList<>();
        for (Doc d : docs) {
            out.add(new Member(d, Doc.NIL));
        }
        return out;
    }

    /** Members with a comma between them, one to a line where they do not fit. The comma stays on
     * the line its member ends, and a comment written at the end of that line follows the comma. */
    private static Doc separated(List<Member> members) {
        List<Doc> parts = new ArrayList<>();
        for (int i = 0; i < members.size(); i++) {
            if (i > 0) {
                parts.add(LINE);
            }
            parts.add(members.get(i).doc());
            if (i < members.size() - 1) {
                parts.add(text(","));
            }
            parts.add(members.get(i).trailing());
        }
        return concat(parts);
    }

    /**
     * Members between brackets. {@code boundary} is what sits just inside them — {@link Doc#LINE}
     * where the flat form has a space there ({@code exposing ( a, b )}, {@code T { a, b }}),
     * {@link Doc#SOFTLINE} where it does not ({@code f(a, b)}, {@code [a, b]}).
     */
    private static Doc delimited(String open, Doc boundary, List<Member> members, String close) {
        return group(concat(text(open),
                nest(INDENT, concat(boundary, separated(members))),
                boundary, text(close)));
    }

    /**
     * One part of a chain, written after the connector that joins it to what came before.
     * {@code leading} is what goes above the line the part opens — its comments. The connector is
     * part of that line, so the two are written in this order and not the other: a comment placed
     * after the connector leaves the part itself starting a line the connector never opened.
     */
    private record Segment(String connector, Doc doc, Doc leading) {

        Segment(String connector, Doc doc) {
            this(connector, doc, Doc.NIL);
        }
    }

    /**
     * A head and the parts written after it, each opening with its connector — a union's {@code |},
     * an operator chain's operator, a pipeline's {@code |>}, an example row's {@code :} and
     * {@code ->}. Broken, each part starts a line one indent in and the connector leads it, so what
     * joins two parts is visible at the front of the second.
     */
    private static Doc chained(Doc head, List<Segment> segments) {
        List<Doc> parts = new ArrayList<>();
        for (Segment s : segments) {
            parts.add(concat(LINE, s.leading(), text(s.connector()), s.doc()));
        }
        return group(concat(head, nest(INDENT, concat(parts))));
    }

    /** {@code docs} as segments sharing one connector — a run of the same operator. */
    private static List<Segment> segments(String connector, List<Doc> docs) {
        List<Segment> out = new ArrayList<>();
        for (Doc d : docs) {
            out.add(new Segment(connector, d));
        }
        return out;
    }

    // --- top level ---

    private Doc file(SyntaxNode file) {
        comments = attach(file);
        List<Doc> parts = new ArrayList<>();
        SyntaxKind prev = null;
        for (SyntaxNode item : file.childNodes()) {
            if (!isTopLevel(item.kind())) {
                continue;
            }
            // A top-level item's comments are read the same way a member's are, and marked written
            // the same way: an `example`'s comment is the item's leading trivia here and the first
            // row's from inside, and it belongs to whichever asks first.
            Doc lead = aboveOf(item);
            if (prev != null) {
                parts.add(HARDLINE);
                if (blankBetween(prev, item.kind())) {
                    parts.add(HARDLINE);
                }
            }
            parts.add(lead);
            parts.add(item(item));
            parts.add(afterOf(item));
            prev = item.kind();
        }
        parts.add(endOf(file));
        parts.add(HARDLINE);   // files end with a single newline
        return concat(parts);
    }

    /** One blank line separates every top-level item, except the module header and its imports,
     * which stay tight together (as gofmt keeps a package clause and its import block). */
    private static boolean blankBetween(SyntaxKind prev, SyntaxKind current) {
        boolean header = (prev == SyntaxKind.MODULE_HEADER || prev == SyntaxKind.IMPORT_DECL)
                && current == SyntaxKind.IMPORT_DECL;
        return !header;
    }

    private static boolean isTopLevel(SyntaxKind k) {
        return k == SyntaxKind.MODULE_HEADER || k == SyntaxKind.IMPORT_DECL
                || k == SyntaxKind.DATA_DEF || k == SyntaxKind.BEHAVIOR_DEF || k == SyntaxKind.FN_DEF
                || k == SyntaxKind.EXAMPLE_DEF || k == SyntaxKind.EXAMPLES_FILE_HEADER
                || k == SyntaxKind.FAKE_DEF;
    }

    private Doc item(SyntaxNode n) {
        return switch (n.kind()) {
            case MODULE_HEADER -> moduleHeader(n);
            case IMPORT_DECL -> importDecl(n);
            case DATA_DEF -> dataDef(n);
            case BEHAVIOR_DEF -> behaviorDef(n);
            case FN_DEF -> fnDef(n);
            case EXAMPLES_FILE_HEADER -> examplesFileHeader(n);
            case EXAMPLE_DEF -> exampleDef(n);
            case FAKE_DEF -> fakeDef(n);
            default -> text(n.text().strip());
        };
    }

    // --- example ---

    private Doc examplesFileHeader(SyntaxNode n) {
        return concat(text("examples for "), qualifiedName(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow()));
    }

    private Doc exampleDef(SyntaxNode n) {
        List<SyntaxToken> ids = idents(n);   // ["example", target]
        String target = ids.size() >= 2 ? ids.get(1).text() : "";
        List<Doc> rows = new ArrayList<>();
        for (SyntaxNode row : childNodes(n, SyntaxKind.EXAMPLE_ROW)) {
            rows.add(concat(HARDLINE, concat(aboveOf(row), exampleRow(row)),
                    afterOf(row)));
        }
        rows.add(endOf(n));
        return concat(text("example "), text(target), nest(INDENT, concat(rows)));
    }

    /**
     * A row of an example: its description, its input and what it is expected to give. The three are
     * the row's own parts, so the row is what breaks when it does not fit — a row that broke inside
     * its input instead left {@code ), Amount(100)) -> Accepted} opening a line, and stopped showing
     * which part was which.
     */
    private Doc exampleRow(SyntaxNode n) {
        Doc input = n.child(SyntaxKind.ARG_LIST)
                .map(a -> delimited("(", SOFTLINE, exprDocs(a), ")"))
                .orElse(text("()"));
        var with = n.child(SyntaxKind.WITH_CLAUSE);
        if (with.isPresent()) {
            List<Member> binds = new ArrayList<>();
            for (SyntaxNode b : childNodes(with.get(), SyntaxKind.WITH_BINDING)) {
                binds.add(member(b, concat(text(firstIdent(b)), text(" = "),
                        expr(firstExprChildOpt(b).orElseThrow()))));
            }
            input = concat(input, text(" with "),
                    group(nest(INDENT, separated(withEndComments(with.get(), binds)))));
        }

        List<Segment> segs = new ArrayList<>();
        var desc = n.token(SyntaxKind.STRING_LIT);
        Doc head;
        if (desc.isPresent()) {
            head = concat(text("| "), text(desc.get().text()));
            segs.add(new Segment(": ", input));
        } else {
            head = concat(text("| "), input);
        }
        List<SyntaxNode> expected = exprChildren(n);   // the row's expr child that is not the ARG_LIST
        segs.add(new Segment("-> ", expected.isEmpty() ? Doc.NIL : expr(expected.get(0))));
        return chained(head, segs);
    }

    private Doc fakeDef(SyntaxNode n) {
        List<SyntaxToken> ids = idents(n);   // ["fake", target]
        String target = ids.size() >= 2 ? ids.get(1).text() : "";
        List<Doc> rows = new ArrayList<>();
        for (SyntaxNode row : childNodes(n, SyntaxKind.FAKE_ROW)) {
            rows.add(concat(HARDLINE, concat(aboveOf(row), fakeRow(row)), afterOf(row)));
        }
        rows.add(endOf(n));
        return concat(text("fake "), text(target), nest(INDENT, concat(rows)));
    }

    private Doc fakeRow(SyntaxNode n) {
        var args = n.child(SyntaxKind.ARG_LIST);
        Doc input;
        if (args.isPresent()) {
            input = delimited("(", SOFTLINE, exprDocs(args.get()), ")");
        } else {
            input = text("_");   // the default row
        }
        List<SyntaxNode> outs = exprChildren(n);
        return chained(concat(text("| "), input),
                List.of(new Segment("-> ", outs.isEmpty() ? Doc.NIL : expr(outs.get(0)))));
    }

    private Doc moduleHeader(SyntaxNode n) {
        Doc d = concat(text("module "), qualifiedName(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow()));
        return n.child(SyntaxKind.EXPOSING_CLAUSE)
                .map(c -> concat(d, text(" "), exposing(c)))
                .orElse(d);
    }

    private Doc exposing(SyntaxNode clause) {
        List<Member> entries = new ArrayList<>();
        for (SyntaxNode e : childNodes(clause, SyntaxKind.EXPOSED_ENTRY)) {
            Doc name = qualifiedName(e.child(SyntaxKind.QUALIFIED_NAME).orElseThrow());
            entries.add(member(e, e.child(SyntaxKind.RET_TYPE)
                    .map(rt -> concat(name, text(" : "), retType(rt)))
                    .orElse(name)));
        }
        return delimited("exposing (", LINE, withEndComments(clause, entries), ")");
    }

    private Doc importDecl(SyntaxNode n) {
        Doc d = concat(text("import "), qualifiedName(n.child(SyntaxKind.QUALIFIED_NAME).orElseThrow()));
        Optional<SyntaxNode> alias = n.child(SyntaxKind.IMPORT_ALIAS);
        if (alias.isPresent()) {
            d = concat(d, text(" as "), text(idents(alias.get()).get(0).text()));
        }
        Optional<SyntaxNode> list = n.child(SyntaxKind.NAME_LIST);
        if (list.isEmpty()) {
            return d;   // an import that only renames the module, or only names the dependency
        }
        List<Member> names = new ArrayList<>();
        for (SyntaxToken t : idents(list.get())) {
            names.add(tokenMember(t, t, text(t.text())));
        }
        return concat(d, text(" "),
                delimited("(", LINE, withEndComments(list.get(), names), ")"));
    }

    // --- data ---

    private Doc dataDef(SyntaxNode n) {
        String name = firstIdent(n);
        List<Doc> invariants = new ArrayList<>();
        for (SyntaxNode inv : childNodes(n, SyntaxKind.INVARIANT_CLAUSE)) {
            // A named clause keeps its name: it is what an attempt's arm and a boundary issue call it.
            String label = inv.token(SyntaxKind.ASSIGN).isPresent()
                    ? firstIdent(inv) + " = " : "";
            invariants.add(concat(HARDLINE,
                    concat(aboveOf(inv), text("invariant " + label), expr(onlyExpr(inv))),
                    afterOf(inv)));
        }

        var product = n.child(SyntaxKind.PRODUCT_BODY);
        if (product.isPresent()) {
            return concat(text("data "), text(name), text(" ="),
                    nest(INDENT, concat(concat(HARDLINE, productBody(product.get())), concat(invariants))));
        }
        var sum = n.child(SyntaxKind.SUM_BODY);
        if (sum.isPresent()) {
            // A sum's cases are bare idents, not nodes, so a case's comments are held against where
            // its identifier is rather than against a member node.
            Doc head = null;
            List<Doc> headComments = new ArrayList<>();
            List<Segment> cases = new ArrayList<>();
            for (SyntaxElement e : sum.get().children()) {
                if (!(e instanceof SyntaxToken t) || t.kind() != SyntaxKind.IDENT) {
                    continue;
                }
                Doc body = concat(text(t.text()), afterCase(t));
                if (head == null) {
                    head = body;
                    headComments = new ArrayList<>();
                    for (Doc c : aboveCase(t)) {
                        headComments.add(concat(c, HARDLINE));
                    }
                } else {
                    List<Doc> lead = new ArrayList<>();
                    for (Doc c : aboveCase(t)) {
                        lead.add(concat(c, HARDLINE));
                    }
                    cases.add(new Segment("| ", body, concat(lead)));
                }
            }
            Doc chain = chained(head, cases);
            if (headComments.isEmpty()) {
                return concat(text("data "), text(name), text(" = "), chain);
            }
            // The first case shares its line with `data S =`, so its comments cannot go above that
            // line without describing the declaration instead. The union moves down a line instead.
            return concat(text("data "), text(name), text(" ="),
                    nest(INDENT, concat(HARDLINE, concat(headComments), chain)));
        }
        var newtype = n.child(SyntaxKind.NEWTYPE_BODY);
        if (newtype.isPresent()) {
            Doc inner = concat(aboveOf(newtype.get()), typeRef(typeChild(newtype.get())),
                    afterOf(newtype.get()));
            return concat(text("data "), text(name), text(" = "), inner, nest(INDENT, concat(invariants)));
        }
        return concat(text("data "), text(name));   // unit
    }

    /** The leading-comma product block: {@code { f1: T1\n, f2: T2\n}}. Always multi-line. */
    private Doc productBody(SyntaxNode body) {
        List<Doc> lines = new ArrayList<>();
        for (SyntaxNode m : body.childNodes()) {
            Doc member;
            if (m.kind() == SyntaxKind.FIELD) {
                member = field(m);
            } else if (m.kind() == SyntaxKind.SPREAD_MEMBER) {
                member = concat(text("..."), text(firstIdent(m)));
            } else {
                continue;
            }
            // The opener is part of the member's line, so it is inside what the comments decorate:
            // a comment written after it would leave the member starting a line of its own, at the
            // block's indent rather than after the comma the rest of the block is written with.
            boolean first = lines.isEmpty();
            Doc line = concat(concat(aboveOf(m), text(first ? "{ " : ", "), member),
                    afterOf(m));
            lines.add(first ? line : concat(HARDLINE, line));
        }
        lines.add(endOf(body));
        lines.add(concat(HARDLINE, text("}")));
        return concat(lines);
    }

    private Doc field(SyntaxNode n) {
        Doc d = concat(text(firstIdent(n)), text(": "), typeRef(typeChild(n)));
        return n.token(SyntaxKind.QUESTION).isPresent() ? concat(d, text("?")) : d;
    }

    // --- behavior ---

    private Doc behaviorDef(SyntaxNode n) {
        String name = firstIdent(n);
        var sig = n.child(SyntaxKind.BEHAVIOR_SIG);
        if (sig.isPresent()) {
            SyntaxNode s = sig.get();
            Doc params = paramList(s.child(SyntaxKind.PARAM_LIST).orElseThrow());
            SyntaxNode retNode = s.child(SyntaxKind.RET_TYPE).orElseThrow();
            Doc ret = concat(aboveOf(retNode), retType(retNode), afterOf(retNode));
            List<Doc> clauses = new ArrayList<>();
            for (SyntaxNode c : s.childNodes()) {
                if (c.kind() == SyntaxKind.CONSTRUCTS_CLAUSE) {
                    clauses.add(concat(HARDLINE,
                            concat(aboveOf(c), text("constructs "), nameList(c, 0)),
                            afterOf(c)));
                } else if (c.kind() == SyntaxKind.DEPENDS_CLAUSE) {
                    clauses.add(concat(HARDLINE,
                            concat(aboveOf(c), text("depends on "), nameList(c, 1)),
                            afterOf(c)));
                }
            }
            return concat(text("behavior "), text(name), text(" : "), params, text(" -> "), ret,
                    nest(INDENT, concat(clauses)));
        }
        SyntaxNode pipe = n.child(SyntaxKind.PIPE_BEHAVIOR).orElseThrow();
        List<SyntaxNode> stages = childNodes(pipe, SyntaxKind.STAGE);
        Doc declaredOut = pipe.child(SyntaxKind.RET_TYPE)
                .map(rt -> concat(text(" -> "), retType(rt))).orElse(Doc.NIL);
        List<Doc> parts = new ArrayList<>();
        for (int i = 0; i < stages.size(); i++) {
            SyntaxNode st = stages.get(i);
            // What the declaration writes after the last stage is on that stage's line, so it comes
            // before the comment that ends the line rather than after it.
            parts.add(concat(LINE, aboveOf(st), text(i == 0 ? "" : ">-> "), stage(st),
                    i == stages.size() - 1 ? declaredOut : Doc.NIL, afterOf(st)));
        }
        return concat(text("behavior "), text(name), text(" ="),
                group(nest(INDENT, concat(parts))));
    }

    private Doc paramList(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode p : childNodes(n, SyntaxKind.PARAM)) {
            params.add(member(p, concat(text(firstIdent(p)), text(": "),
                    retType(p.child(SyntaxKind.RET_TYPE).orElseThrow()))));
        }
        return delimited("(", SOFTLINE, withEndComments(n, params), ")");
    }

    private Doc stage(SyntaxNode n) {
        StringBuilder sb = new StringBuilder();
        for (SyntaxToken t : idents(n)) {
            if (sb.length() > 0) {
                sb.append('.');
            }
            sb.append(t.text());
        }
        return text(sb.toString());
    }

    /** The names a {@code constructs} / {@code depends on} clause lists. {@code skipIdents} drops
     * the leading identifiers that belong to the keyword rather than the list — the {@code on} of
     * {@code depends on}, which lexes as an ordinary identifier. */
    private Doc nameList(SyntaxNode clause, int skipIdents) {
        // an entry may name through a module, so the dots of one name are kept and only a comma
        // starts the next
        List<Member> names = new ArrayList<>();
        StringBuilder current = new StringBuilder();
        SyntaxToken opened = null;
        SyntaxToken ended = null;
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
                case IDENT -> {
                    if (opened == null) {
                        opened = t;
                    }
                    ended = t;
                    current.append(t.text());
                }
                case DOT -> current.append('.');
                case COMMA -> {
                    names.add(tokenMember(opened, ended, text(current.toString())));
                    current.setLength(0);
                    opened = null;
                    ended = null;
                }
                default -> { }   // the `constructs` / `depends` keyword
            }
        }
        if (current.length() > 0) {
            names.add(tokenMember(opened, ended, text(current.toString())));
        }
        return group(nest(INDENT, separated(withEndComments(clause, names))));
    }

    /** The {@code : T} a node wrote, or nothing — a helper's return type, a local binding's annotation. */
    private Doc writtenType(SyntaxNode n) {
        return n.child(SyntaxKind.RET_TYPE).map(rt -> concat(text(": "), retType(rt))).orElse(Doc.NIL);
    }

    // --- fn ---

    private Doc fnDef(SyntaxNode n) {
        String name = firstIdent(n);
        // The modifiers are written back in the order the parser reads them: `private partial let`.
        String modifiers = (n.child(SyntaxKind.PRIVATE_MODIFIER).isPresent() ? "private " : "")
                + (n.child(SyntaxKind.PARTIAL_MODIFIER).isPresent() ? "partial " : "");
        Doc keyword = text(modifiers + "let ");
        var written = n.child(SyntaxKind.FN_PARAM_LIST);
        // A lambda on the right of `=` is the parameter-list form written the other way round, so it
        // is written back with its parameters on the left. A definition with neither is a value, and
        // writes no list at all.
        SyntaxNode lifted = written.isPresent() ? null : liftedLambda(n);
        Doc params = written.isPresent() ? concat(text(" "), fnParamList(written.get()))
                : lifted == null ? Doc.NIL : concat(text(" "), lambdaParams(lifted));
        Doc head = concat(keyword, text(name), params, writtenType(n));

        var intrinsic = n.child(SyntaxKind.INTRINSIC_BODY);
        if (intrinsic.isPresent()) {
            String raw = intrinsic.get().token(SyntaxKind.STRING_LIT).orElseThrow().text();
            return concat(head, text(" ="),
                    group(nest(INDENT, concat(LINE, text("intrinsic "), text(raw)))));
        }
        var block = n.child(SyntaxKind.BLOCK_EXPR);
        if (block.isPresent()) {
            return concat(head, text(" = "), block(block.get()));
        }
        SyntaxNode body = lifted == null ? onlyExpr(n) : lastExprChild(lifted);
        return concat(head, text(" ="), group(nest(INDENT, concat(LINE, expr(body)))));
    }

    /** The lambda a parameter-less definition was written as, or null when its body is an ordinary
     * expression and the definition is a value. */
    private SyntaxNode liftedLambda(SyntaxNode n) {
        if (n.child(SyntaxKind.BLOCK_EXPR).isPresent() || n.child(SyntaxKind.INTRINSIC_BODY).isPresent()) {
            return null;
        }
        SyntaxNode body = onlyExpr(n);
        return body.kind() == SyntaxKind.LAMBDA_EXPR ? body : null;
    }

    /** A lambda's parameters as a definition's parameter list — always parenthesised, which is the
     * only shape a definition writes. */
    private Doc lambdaParams(SyntaxNode lambda) {
        List<Doc> params = new ArrayList<>();
        for (SyntaxNode c : lambda.childNodes()) {
            if (isPatternNode(c.kind())) {
                params.add(pattern(c));
            }
        }
        return delimited("(", SOFTLINE, plain(params), ")");
    }

    private Doc fnParamList(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode p : childNodes(n, SyntaxKind.FN_PARAM)) {
            SyntaxNode pat = optionalPatternChild(p);
            Doc d = pat == null ? text(firstIdent(p)) : pattern(pat);
            var rt = p.child(SyntaxKind.RET_TYPE);
            if (rt.isPresent()) {
                d = concat(d, text(": "), retType(rt.get()));
            }
            params.add(member(p, d));
        }
        return delimited("(", SOFTLINE, withEndComments(n, params), ")");
    }

    // --- types ---

    private Doc fnType(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        Doc result = Doc.NIL;
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
        return concat(delimited("(", SOFTLINE, params, ")"), text(" -> "), result);
    }

    private Doc retType(SyntaxNode n) {
        List<Doc> cases = new ArrayList<>();
        List<Segment> rest = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (!isTypeNode(c.kind())) {
                continue;
            }
            Doc body = concat(typeTerm(c), afterOf(c));
            if (cases.isEmpty()) {
                cases.add(concat(aboveOf(c), body));
            } else {
                rest.add(new Segment("| ", body, aboveOf(c)));
            }
        }
        Doc d = cases.isEmpty() ? Doc.NIL : chained(cases.get(0), rest);
        // `T?` in a core signature, the same mark a field carries
        return n.token(SyntaxKind.QUESTION).isPresent() ? concat(d, text("?")) : d;
    }

    private Doc typeRef(SyntaxNode n) {
        if (n.kind() == SyntaxKind.TUPLE_TYPE) {
            List<Member> elems = new ArrayList<>();
            for (SyntaxNode c : n.childNodes()) {
                if (isTypeNode(c.kind())) {
                    elems.add(member(c, typeTerm(c)));
                }
            }
            return delimited("(", SOFTLINE, withEndComments(n, elems), ")");
        }
        var typevar = n.token(SyntaxKind.TYPEVAR);
        if (typevar.isPresent()) {
            return text(typevar.get().text());
        }
        Doc name = qualifiedName(n);   // a type may be named through its module or an import alias
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
        return concat(name, delimited("<", SOFTLINE, withEndComments(args.get(), typeArgs), ">"));
    }

    private static boolean isTypeNode(SyntaxKind k) {
        return k == SyntaxKind.TYPE_REF || k == SyntaxKind.TUPLE_TYPE || k == SyntaxKind.FN_TYPE;
    }

    /** One term of a written type. A function type reads as itself wherever a type goes. */
    private Doc typeTerm(SyntaxNode n) {
        return n.kind() == SyntaxKind.FN_TYPE ? fnType(n) : typeRef(n);
    }

    // --- expressions ---

    private Doc expr(SyntaxNode n) {
        return switch (n.kind()) {
            case LITERAL_EXPR -> text(firstMeaningfulToken(n).text());
            case VAR_EXPR -> text(firstIdent(n));
            case FIELD_ACCESS -> concat(expr(firstExprChild(n)), text("."), text(lastIdent(n)));
            case FIELD_GETTER -> concat(text("."), text(lastIdent(n)));
            case APPLY_EXPR -> apply(n);
            case BINARY_EXPR -> binary(n);
            case UNARY_EXPR -> concat(text("-"), expr(onlyExpr(n)));
            case PIPE_EXPR -> pipe(n);
            case PAREN_EXPR -> concat(text("("), expr(onlyExpr(n)), text(")"));
            case TUPLE_EXPR -> delimited("(", SOFTLINE, exprDocs(n), ")");
            case LIST_EXPR -> list(n);
            case LIST_COMP -> listComp(n);
            case IF_EXPR -> ifExpr(n);
            case MATCH_EXPR -> matchExpr(n);
            case LAMBDA_EXPR -> lambda(n);
            case NEW_DATA_EXPR -> newData(n);
            case BLOCK_EXPR -> block(n);
            case UNREACHABLE_EXPR -> concat(text("unreachable "), expr(onlyExpr(n)));
            default -> text(n.text().strip());
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
    private Doc apply(SyntaxNode n) {
        return concat(expr(firstExprChild(n)), arguments(n));
    }

    /** The bracketed argument list of a call or an application. */
    private Doc arguments(SyntaxNode n) {
        List<SyntaxNode> args = n.child(SyntaxKind.ARG_LIST).map(this::exprChildren).orElse(List.of());
        SyntaxNode argList = n.child(SyntaxKind.ARG_LIST).orElse(null);
        if (args.isEmpty()) {
            List<Member> only = argList == null ? List.of() : withEndComments(argList, List.of());
            return only.isEmpty() ? text("()") : delimited("(", SOFTLINE, only, ")");
        }
        List<Member> argDocs = new ArrayList<>();
        for (SyntaxNode a : args) {
            argDocs.add(member(a, expr(a)));
        }
        return delimited("(", SOFTLINE, withEndComments(argList, argDocs), ")");
    }

    private Doc binary(SyntaxNode n) {
        List<Segment> segs = new ArrayList<>();
        Doc head = collectChain(n, ladderLevel(operatorKind(n)), segs);
        return chained(head, segs);
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
    private Doc collectChain(SyntaxNode n, int level, List<Segment> segs) {
        List<SyntaxNode> ops = exprChildren(n);
        SyntaxNode left = ops.get(0);
        Doc head;
        if (left.kind() == SyntaxKind.BINARY_EXPR && ladderLevel(operatorKind(left)) == level) {
            head = collectChain(left, level, segs);
        } else {
            head = concat(aboveOf(left), expr(left), afterOf(left));
        }
        SyntaxNode right = ops.get(1);
        segs.add(new Segment(operatorText(n) + " ", concat(expr(right), afterOf(right)),
                aboveOf(right)));
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

    private Doc pipe(SyntaxNode n) {
        List<Segment> stages = new ArrayList<>();
        Doc head = collectPipe(n, stages);
        return chained(head, stages);
    }

    /** Flattens a left-nested {@code |>} chain: returns the head doc and fills {@code stages} with each
     * right-hand stage in source order. */
    private Doc collectPipe(SyntaxNode n, List<Segment> stages) {
        List<SyntaxNode> ops = exprChildren(n);
        SyntaxNode left = ops.get(0);
        SyntaxNode right = ops.get(1);
        Doc head;
        if (left.kind() == SyntaxKind.PIPE_EXPR) {
            head = collectPipe(left, stages);
        } else {
            head = concat(aboveOf(left), expr(left), afterOf(left));
        }
        stages.add(new Segment("|> ", concat(expr(right), afterOf(right)), aboveOf(right)));
        return head;
    }

    private Doc list(SyntaxNode n) {
        List<Member> elems = exprDocs(n);
        if (elems.isEmpty()) {
            return text("[]");   // exprDocs has already asked for what was written inside
        }
        return delimited("[", SOFTLINE, elems, "]");
    }

    private Doc listComp(SyntaxNode n) {
        List<Member> exprs = exprDocs(n);
        Member element = exprs.get(0);
        List<Member> guards = exprs.subList(1, exprs.size());
        // The `|` is the comprehension's and it is on the element's line, so it goes before the
        // comment that ends that line — as a comma does for a member of a list.
        return group(concat(text("["), element.doc(), text(" |"), element.trailing(),
                nest(INDENT, concat(LINE, separated(guards))), SOFTLINE, text("]")));
    }

    private Doc ifExpr(SyntaxNode n) {
        List<SyntaxNode> parts = exprChildren(n);
        Doc departures = elseArms(n);
        return group(concat(text("if "), expr(parts.get(0)), attemptBinder(n), text(" then"),
                nest(INDENT, concat(LINE, expr(parts.get(1)))),
                LINE, text("else"),
                departures != Doc.NIL
                        ? departures
                        : nest(INDENT, concat(LINE, expr(parts.get(2))))));
    }

    /** An attempt's per-clause departures, one to a line under the {@code else}, or nothing where the
     * {@code else} took one expression. */
    private Doc elseArms(SyntaxNode n) {
        var arms = n.child(SyntaxKind.ELSE_ARMS);
        if (arms.isEmpty()) {
            return Doc.NIL;
        }
        List<Doc> lines = new ArrayList<>();
        for (SyntaxNode arm : childNodes(arms.get(), SyntaxKind.ELSE_ARM)) {
            lines.add(concat(HARDLINE, aboveOf(arm), text("| " + firstIdent(arm) + " -> "),
                    expr(onlyExpr(arm)), afterOf(arm)));
        }
        lines.add(endOf(arms.get()));
        return nest(INDENT, concat(lines));
    }

    /** The {@code as x} of an attempted construction, or nothing where none was written. It sits
     * between the construction and the {@code then}/{@code else} that follows it. */
    private Doc attemptBinder(SyntaxNode n) {
        boolean afterAs = false;
        for (SyntaxElement e : meaningful(n)) {
            if (!(e instanceof SyntaxToken t)) continue;
            if (t.kind() == SyntaxKind.AS_KW) {
                afterAs = true;
            } else if (afterAs && t.kind() == SyntaxKind.IDENT) {
                return text(" as " + t.text());
            }
        }
        return Doc.NIL;
    }

    private Doc matchExpr(SyntaxNode n) {
        SyntaxNode scrutinee = exprChildren(n).get(0);
        List<Doc> cases = new ArrayList<>();
        for (SyntaxNode c : childNodes(n, SyntaxKind.MATCH_CASE)) {
            cases.add(concat(HARDLINE, concat(aboveOf(c), matchCase(c)), afterOf(c)));
        }
        cases.add(endOf(n));
        return concat(text("match "), expr(scrutinee), text(" with"), nest(INDENT, concat(cases)));
    }

    private Doc matchCase(SyntaxNode n) {
        StringBuilder pattern = new StringBuilder();
        SyntaxNode body = null;
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
                // a qualified case name is one name: no space around its dots
                boolean joined = pattern.length() > 0
                        && (t.kind() == SyntaxKind.DOT || pattern.charAt(pattern.length() - 1) == '.');
                if (pattern.length() > 0 && t.kind() != SyntaxKind.COMMA && !joined) {
                    pattern.append(' ');
                }
                pattern.append(t.text());
            }
        }
        return chained(concat(text("| "), text(pattern.toString())),
                List.of(new Segment("-> ", expr(body))));
    }

    private Doc lambda(SyntaxNode n) {
        List<Doc> params = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isPatternNode(c.kind())) {
                params.add(pattern(c));
            }
        }
        // `x -> e` keeps its bare parameter; anything parenthesised was written that way
        Doc paramsDoc = n.token(SyntaxKind.LPAREN).isPresent()
                ? delimited("(", SOFTLINE, plain(params), ")")
                : params.get(0);
        return concat(paramsDoc, text(" -> "), expr(lastExprChild(n)));
    }

    private Doc newData(SyntaxNode n) {
        String typeName = firstIdent(n);
        List<Member> members = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            Doc member;
            if (c.kind() == SyntaxKind.SPREAD_MEMBER) {
                member = concat(text("..."), text(identPath(c)));   // `...c` or `...c.address`
            } else if (c.kind() == SyntaxKind.FIELD_INIT) {
                var value = firstExprChildOpt(c);
                member = value.map(v -> concat(text(firstIdent(c)), text(" = "), expr(v)))
                        .orElse(text(firstIdent(c)));   // shorthand `field`
            } else {
                continue;
            }
            // A member's leading comments come before it, each on its own line. The HARDLINE forces
            // the enclosing group to break, which is what a literal with a comment in it wants
            // anyway: a `//` on a line the group had collapsed would swallow the rest of it.
            members.add(member(c, member));
        }
        if (members.isEmpty()) {
            List<Member> only = withEndComments(n, List.of());
            return only.isEmpty() ? concat(text(typeName), text(" {}"))
                    : concat(text(typeName), text(" "), delimited("{", LINE, only, "}"));
        }
        return concat(text(typeName), text(" "),
                delimited("{", LINE, withEndComments(n, members), "}"));
    }

    private Doc block(SyntaxNode n) {
        List<Doc> lines = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            // A statement inside a block carries its leading comments the same way a top-level item
            // does. Walking only the child nodes dropped them, so a comment explaining a step was
            // lost on the first format.
            Doc lead = aboveOf(c);
            Doc d = switch (c.kind()) {
                case LET_STMT -> concat(text("let "), text(firstIdent(c)), writtenType(c),
                        text(" = "), expr(onlyExpr(c)));
                case LET_DESTRUCTURE -> concat(text("let "), pattern(patternChild(c)),
                        text(" = "), expr(onlyExpr(c)));
                case GUARD_STMT -> guardStmt(c);
                default -> expr(c);   // the result expression
            };
            lines.add(concat(HARDLINE, lead, d, afterOf(c)));
        }
        lines.add(endOf(n));
        return concat(text("{"), nest(INDENT, concat(lines)), HARDLINE, text("}"));
    }

    /** A binding pattern, written back as it was: a name, a tuple, a newtype opened by its
     * constructor, or a record's fields. */
    private Doc pattern(SyntaxNode n) {
        switch (n.kind()) {
            case PATTERN_NAME -> {
                return text(firstIdent(n));
            }
            case PATTERN_TUPLE -> {
                List<Doc> elems = new ArrayList<>();
                for (SyntaxNode c : n.childNodes()) {
                    if (isPatternNode(c.kind())) {
                        elems.add(pattern(c));
                    }
                }
                return delimited("(", SOFTLINE, plain(elems), ")");
            }
            case PATTERN_CTOR -> {
                return concat(qualifiedName(n), text("("), pattern(patternChild(n)), text(")"));
            }
            case PATTERN_RECORD -> {
                List<Doc> fields = new ArrayList<>();
                for (SyntaxNode f : n.childNodes()) {
                    if (f.kind() != SyntaxKind.PATTERN_FIELD) {
                        continue;
                    }
                    List<SyntaxToken> names = idents(f);
                    fields.add(names.size() > 1
                            ? concat(text(names.get(0).text()), text(" = "), text(names.get(1).text()))
                            : text(names.get(0).text()));
                }
                return delimited("{", LINE, plain(fields), "}");
            }
            default -> {
                return text(firstIdent(n));
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

    private Doc guardStmt(SyntaxNode n) {
        List<SyntaxNode> exprs = exprChildren(n);
        Doc departures = elseArms(n);
        if (departures != Doc.NIL) {
            return concat(text("guard "), expr(exprs.get(0)), attemptBinder(n), text(" else"),
                    departures);
        }
        return concat(text("guard "), expr(exprs.get(0)), attemptBinder(n),
                text(" else "), expr(exprs.get(1)));
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
            default -> false;
        };
    }

    /** What opens a construct. It is the construct's too, so a comment written above it was written
     * above the first member rather than above the bracket — which is also what keeps the answer
     * the same on a second formatting, when the bracket has moved onto the member's line. */
    private static boolean opens(SyntaxToken t) {
        return switch (t.kind()) {
            case LBRACE, LPAREN, LBRACKET -> true;
            default -> false;
        };
    }

    /** The code the comment at {@code i} was written above, or null where the file ends first. */
    private static SyntaxToken nextCode(List<SyntaxToken> all, int i) {
        for (int j = i + 1; j < all.size(); j++) {
            SyntaxToken t = all.get(j);
            if (t.isTrivia() || separates(t)) {
                continue;
            }
            return t.kind() == SyntaxKind.EOF ? null : t;
        }
        return null;
    }

    /** The code a comment was written after. */
    private static SyntaxToken lastCode(List<SyntaxToken> code) {
        for (int i = code.size() - 1; i >= 0; i--) {
            if (!separates(code.get(i))) {
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
        if (next != null && opens(next)) {
            // what opens a construct is the construct's, and it shares a line with the first member
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
            place(out, beginningAt(next), comment, true);
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
        if (isBareMember(code) && code.end() != code.parent().end()) {
            out.afterCase().computeIfAbsent(nameEnd(code), _ -> new ArrayList<>()).add(comment);
            return;
        }
        place(out, endingAt(code), comment, false);
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
        SyntaxNode from = owner;
        // A run the layout flattens is written as segments, and a part of the spine ends where its
        // own segment does rather than where the whole run does. Only inside the run, though: the
        // last segment of the outermost run is followed by whatever the construct holding it writes
        // — a `then`, a closing bracket — and a comment there would have that written inside it.
        while (isSpine(from) && from.parent() != null && from.parent().kind() == from.kind()) {
            from = lastSegmentOf(from);
        }
        for (SyntaxNode c = from; c != null && c.parent() != null; c = c.parent()) {
            if (takesALineOf(c.parent().kind(), c.kind())) {
                add(above ? out.above() : out.after(), c, comment);
                return;
            }
        }
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
        return switch (t.kind()) {
            case RBRACE, RPAREN, RBRACKET -> holdsLines(t.parent().kind());
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

    /** Whether a {@code child} of {@code parent} is written on a line of its own. These are the
     * places a construct is asked for its comments; one added to a list here without being asked is
     * what counting the comments consumed against the comments the tree holds is there to catch. */
    private static boolean takesALineOf(SyntaxKind parent, SyntaxKind child) {
        return switch (parent) {
            case SOURCE_FILE -> isTopLevel(child);
            case PRODUCT_BODY, NEW_DATA_EXPR ->
                    child == SyntaxKind.FIELD || child == SyntaxKind.FIELD_INIT
                            || child == SyntaxKind.SPREAD_MEMBER;
            case MATCH_EXPR -> child == SyntaxKind.MATCH_CASE;
            case EXAMPLE_DEF -> child == SyntaxKind.EXAMPLE_ROW;
            case FAKE_DEF -> child == SyntaxKind.FAKE_ROW;
            case EXPOSING_CLAUSE -> child == SyntaxKind.EXPOSED_ENTRY;
            case PARAM_LIST -> child == SyntaxKind.PARAM;
            case FN_PARAM_LIST -> child == SyntaxKind.FN_PARAM;
            case WITH_CLAUSE -> child == SyntaxKind.WITH_BINDING;
            case ELSE_ARMS -> child == SyntaxKind.ELSE_ARM;
            case PIPE_BEHAVIOR -> child == SyntaxKind.STAGE;
            case DATA_DEF -> child == SyntaxKind.INVARIANT_CLAUSE
                    || child == SyntaxKind.NEWTYPE_BODY;
            case BEHAVIOR_SIG -> child == SyntaxKind.CONSTRUCTS_CLAUSE
                    || child == SyntaxKind.DEPENDS_CLAUSE || child == SyntaxKind.RET_TYPE;
            case RET_TYPE, TYPE_ARGS, TUPLE_TYPE -> isTypeNode(child);
            case FN_TYPE -> child == SyntaxKind.RET_TYPE;
            case BINARY_EXPR -> isExprKind(child) && child != SyntaxKind.BINARY_EXPR;
            case BLOCK_EXPR -> true;
            case ARG_LIST, LIST_EXPR, TUPLE_EXPR, LIST_COMP -> isExprKind(child);
            case PIPE_EXPR -> isExprKind(child) && child != SyntaxKind.PIPE_EXPR;
            default -> false;
        };
    }

    /** Whether a construct writes its members one to a line, so that its closer opens a line a
     * comment can be written on. */
    private static boolean holdsLines(SyntaxKind k) {
        return switch (k) {
            case PRODUCT_BODY, NEW_DATA_EXPR, EXPOSING_CLAUSE, PARAM_LIST, FN_PARAM_LIST, ARG_LIST,
                 LIST_EXPR, TUPLE_EXPR, LIST_COMP, BLOCK_EXPR -> true;
            default -> false;
        };
    }

    // --- writing them back ---

    /** {@code run} as documents, each marked consumed as it is taken. A comment is taken once. */
    private List<Doc> unwritten(List<SyntaxToken> run) {
        List<Doc> out = new ArrayList<>();
        for (SyntaxToken c : run) {
            if (consumedComments.add(c.start())) {
                out.add(text(c.text().stripTrailing()));
            }
        }
        return out;
    }

    /** The comments written above {@code n}, each on its own line in front of it. The
     * {@link Doc#HARDLINE} after each forces the enclosing group to break: a {@code //} on a line the
     * group had collapsed would swallow everything after it. */
    private Doc aboveOf(SyntaxNode n) {
        List<Doc> parts = new ArrayList<>();
        for (Doc c : unwritten(comments.above().getOrDefault(n, List.of()))) {
            parts.add(concat(c, HARDLINE));
        }
        return concat(parts);
    }

    /** The comment written at the end of {@code n}'s line. */
    private Doc afterOf(SyntaxNode n) {
        List<Doc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.after().getOrDefault(n, List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(Doc.trailing(c.text().stripTrailing()));
            }
        }
        return concat(parts);
    }

    /** The comments written inside {@code n} under its last member, each opening a line. */
    private Doc endOf(SyntaxNode n) {
        List<Doc> parts = new ArrayList<>();
        for (Doc c : endLines(n)) {
            parts.add(concat(HARDLINE, c));
        }
        return concat(parts);
    }

    private List<Doc> endLines(SyntaxNode n) {
        return unwritten(comments.atEnd().getOrDefault(n, List.of()));
    }

    /** The comments written above a sum's case, which is an identifier and not a node. */
    private List<Doc> aboveCase(SyntaxToken ident) {
        return unwritten(comments.aboveCase().getOrDefault(ident.start(), List.of()));
    }

    /** The comment written at the end of a sum case's line. */
    private Doc afterCase(SyntaxToken ident) {
        List<Doc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.afterCase().getOrDefault(ident.end(), List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(Doc.trailing(c.text().stripTrailing()));
            }
        }
        return concat(parts);
    }

    /** A member the grammar wrote as an identifier: the same shape as one written as a node, held
     * against where the identifier is. */
    private Member tokenMember(SyntaxToken above, SyntaxToken end, Doc d) {
        List<Doc> lead = new ArrayList<>();
        for (Doc c : unwritten(comments.aboveCase().getOrDefault(nameStart(above), List.of()))) {
            lead.add(concat(c, HARDLINE));
        }
        List<Doc> parts = new ArrayList<>();
        for (SyntaxToken c : comments.afterCase().getOrDefault(nameEnd(end), List.of())) {
            if (consumedComments.add(c.start())) {
                parts.add(Doc.trailing(c.text().stripTrailing()));
            }
        }
        return new Member(concat(concat(lead), d), concat(parts));
    }

    /** A member: what is written above its line, the member, and what ends that line — the last kept
     * apart because whatever the enclosing construct writes between this member and the next belongs
     * on this line, before the comment. */
    private Member member(SyntaxNode node, Doc d) {
        return new Member(concat(aboveOf(node), d), afterOf(node));
    }

    /** {@code members} of {@code parent} with the comments written under the last of them. A
     * construct with no members at all still has somewhere to put them: between its brackets, which
     * is where they were written. */
    private List<Member> withEndComments(SyntaxNode parent, List<Member> members) {
        List<Doc> end = endLines(parent);
        if (end.isEmpty()) {
            return members;
        }
        List<Doc> lines = new ArrayList<>();
        for (Doc c : end) {
            lines.add(concat(HARDLINE, c));
        }
        List<Member> out = new ArrayList<>(members);
        if (out.isEmpty()) {
            // a construct with no members still has between its brackets, which is where they were
            // written; the comments stand where a member would have, so they bring no line of their
            // own — the brackets already open and close one
            out.add(new Member(concat(Doc.MUST_BREAK, Doc.join(HARDLINE, end)), Doc.NIL));
            return out;
        }
        Member last = out.get(out.size() - 1);
        out.set(out.size() - 1,
                new Member(concat(last.doc(), last.trailing(), concat(lines)), Doc.NIL));
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

    private Doc qualifiedName(SyntaxNode n) {
        StringBuilder sb = new StringBuilder();
        for (SyntaxToken t : idents(n)) {
            if (sb.length() > 0) {
                sb.append('.');
            }
            sb.append(t.text());
        }
        return text(sb.toString());
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

    /** Every identifier of a node, dotted — a spread's field path ({@code c.address}). */
    private String identPath(SyntaxNode n) {
        List<String> parts = new ArrayList<>();
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.IDENT) {
                parts.add(t.text());
            }
        }
        if (parts.isEmpty()) {
            throw new IllegalStateException("no identifier in " + n.kind());
        }
        return String.join(".", parts);
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
