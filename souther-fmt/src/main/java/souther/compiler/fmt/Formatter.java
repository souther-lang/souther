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

    /** {@link #commentsBefore} per parent, computed once. It is asked for every member of a parent,
     * and answering means walking that parent's children, so without this a construct with n members
     * walks them n times. One instance formats one file, so the cache lives exactly as long as the
     * tree it describes. */
    private final Map<SyntaxNode, ParentComments> commentsByParent = new IdentityHashMap<>();

    /** The comments written at the end of a line of code, by the construct that line belongs to.
     * Computed once for the file: which of the two a comment is depends on the whitespace before it,
     * which is a fact about the token stream rather than about any one parent. */
    private Map<SyntaxNode, List<SyntaxToken>> trailing = new IdentityHashMap<>();

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

    /** Formats an already-parsed file into its canonical form — for a caller that has parsed the
     * source (e.g. to check for syntax errors) and need not parse it again. Assumes {@code file}
     * came from a clean parse. */
    public static String format(SyntaxNode file) {
        try {
            return new Formatter().file(file).render(WIDTH);
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
        trailing = scanTrailing(file);
        List<Doc> parts = new ArrayList<>();
        SyntaxKind prev = null;
        for (SyntaxNode item : file.childNodes()) {
            if (!isTopLevel(item.kind())) {
                continue;
            }
            // A top-level item's comments are read the same way a member's are, and marked written
            // the same way: an `example`'s comment is the item's leading trivia here and the first
            // row's from inside, and it belongs to whichever asks first.
            List<SyntaxToken> lead = new ArrayList<>(
                    commentsBefore(file).getOrDefault(item, List.of()));
            lead.addAll(leadingDeep(item));
            if (prev != null) {
                parts.add(HARDLINE);
                if (blankBetween(prev, item.kind())) {
                    parts.add(HARDLINE);
                }
            }
            for (Doc c : unwritten(lead)) {
                parts.add(c);
                parts.add(HARDLINE);
            }
            parts.add(item(item));
            for (Doc c : trailingOf(item)) {
                parts.add(c);
            }
            prev = item.kind();
        }
        for (Doc c : unwritten(trailingComments(file))) {
            parts.add(HARDLINE);
            parts.add(c);
        }
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
            rows.add(concat(HARDLINE, withComments(n, row, exampleRow(row)),
                    concat(trailingOf(row))));
        }
        rows.add(endComments(n));
        return concat(text("example "), text(target), nest(INDENT, concat(rows)));
    }

    /**
     * A row of an example: its description, its input and what it is expected to give. The three are
     * the row's own parts, so the row is what breaks when it does not fit — a row that broke inside
     * its input instead left {@code ), Amount(100)) -> Accepted} opening a line, and stopped showing
     * which part was which.
     */
    private Doc exampleRow(SyntaxNode n) {
        List<Doc> args = new ArrayList<>();
        for (SyntaxNode a : n.child(SyntaxKind.ARG_LIST).map(this::exprChildren).orElse(List.of())) {
            args.add(expr(a));
        }
        Doc input = delimited("(", SOFTLINE, plain(args), ")");
        var with = n.child(SyntaxKind.WITH_CLAUSE);
        if (with.isPresent()) {
            List<Doc> binds = new ArrayList<>();
            for (SyntaxNode b : childNodes(with.get(), SyntaxKind.WITH_BINDING)) {
                binds.add(concat(text(firstIdent(b)), text(" = "), expr(firstExprChildOpt(b).orElseThrow())));
            }
            input = concat(input, text(" with "), group(nest(INDENT, separated(plain(binds)))));
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
            rows.add(concat(HARDLINE, withComments(n, row, fakeRow(row)), concat(trailingOf(row))));
        }
        rows.add(endComments(n));
        return concat(text("fake "), text(target), nest(INDENT, concat(rows)));
    }

    private Doc fakeRow(SyntaxNode n) {
        var args = n.child(SyntaxKind.ARG_LIST);
        Doc input;
        if (args.isPresent()) {
            List<Doc> as = new ArrayList<>();
            for (SyntaxNode a : exprChildren(args.get())) {
                as.add(expr(a));
            }
            input = delimited("(", SOFTLINE, plain(as), ")");
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
            entries.add(member(clause, e, e.child(SyntaxKind.RET_TYPE)
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
        List<Doc> names = new ArrayList<>();
        for (SyntaxToken t : idents(list.get())) {
            names.add(text(t.text()));
        }
        return concat(d, text(" "), delimited("(", LINE, plain(names), ")"));
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
                    withComments(n, inv, concat(text("invariant " + label), expr(onlyExpr(inv)))),
                    concat(trailingOf(inv))));
        }

        var product = n.child(SyntaxKind.PRODUCT_BODY);
        if (product.isPresent()) {
            return concat(text("data "), text(name), text(" ="),
                    nest(INDENT, concat(concat(HARDLINE, productBody(product.get())), concat(invariants))));
        }
        var sum = n.child(SyntaxKind.SUM_BODY);
        if (sum.isPresent()) {
            // A sum's cases are bare idents, not nodes, so the comments between them are picked up
            // from the token stream rather than from a member node.
            List<Doc> pending = new ArrayList<>();
            Doc head = null;
            List<Doc> headComments = List.of();
            List<Segment> cases = new ArrayList<>();
            for (SyntaxElement e : sum.get().children()) {
                if (!(e instanceof SyntaxToken t)) {
                    continue;
                }
                if (t.kind() == SyntaxKind.LINE_COMMENT) {
                    for (Doc c : unwritten(List.of(t))) {
                        pending.add(concat(c, HARDLINE));
                    }
                } else if (t.kind() == SyntaxKind.IDENT) {
                    if (head == null) {
                        head = text(t.text());
                        headComments = List.copyOf(pending);
                    } else {
                        cases.add(new Segment("| ", text(t.text()), concat(pending)));
                    }
                    pending.clear();
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
            Doc inner = typeRef(typeChild(newtype.get()));
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
            Doc line = concat(withComments(body, m, concat(text(first ? "{ " : ", "), member)),
                    concat(trailingOf(m)));
            lines.add(first ? line : concat(HARDLINE, line));
        }
        lines.add(endComments(body));
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
            Doc ret = retType(s.child(SyntaxKind.RET_TYPE).orElseThrow());
            List<Doc> clauses = new ArrayList<>();
            for (SyntaxNode c : s.childNodes()) {
                if (c.kind() == SyntaxKind.CONSTRUCTS_CLAUSE) {
                    clauses.add(concat(HARDLINE,
                            withComments(s, c, concat(text("constructs "), nameList(c, 0))),
                            concat(trailingOf(c))));
                } else if (c.kind() == SyntaxKind.DEPENDS_CLAUSE) {
                    clauses.add(concat(HARDLINE,
                            withComments(s, c, concat(text("depends on "), nameList(c, 1))),
                            concat(trailingOf(c))));
                }
            }
            return concat(text("behavior "), text(name), text(" : "), params, text(" -> "), ret,
                    nest(INDENT, concat(clauses)));
        }
        SyntaxNode pipe = n.child(SyntaxKind.PIPE_BEHAVIOR).orElseThrow();
        List<SyntaxNode> stages = childNodes(pipe, SyntaxKind.STAGE);
        List<Doc> tail = new ArrayList<>();
        for (int i = 1; i < stages.size(); i++) {
            tail.add(concat(LINE, text(">-> "), stage(stages.get(i))));
        }
        Doc body = group(nest(INDENT, concat(LINE, stage(stages.get(0)), concat(tail))));
        Doc declaredOut = pipe.child(SyntaxKind.RET_TYPE)
                .map(rt -> concat(text(" -> "), retType(rt))).orElse(Doc.NIL);
        return concat(text("behavior "), text(name), text(" ="), body, declaredOut);
    }

    private Doc paramList(SyntaxNode n) {
        List<Member> params = new ArrayList<>();
        for (SyntaxNode p : childNodes(n, SyntaxKind.PARAM)) {
            params.add(member(n, p, concat(text(firstIdent(p)), text(": "),
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
        List<Doc> names = new ArrayList<>();
        StringBuilder current = new StringBuilder();
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
                case IDENT -> current.append(t.text());
                case DOT -> current.append('.');
                case COMMA -> {
                    names.add(text(current.toString()));
                    current.setLength(0);
                }
                default -> { }   // the `constructs` / `depends` keyword
            }
        }
        if (current.length() > 0) {
            names.add(text(current.toString()));
        }
        return group(nest(INDENT, separated(plain(names))));
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
        List<Doc> params = new ArrayList<>();
        for (SyntaxNode p : childNodes(n, SyntaxKind.FN_PARAM)) {
            SyntaxNode pat = optionalPatternChild(p);
            Doc d = pat == null ? text(firstIdent(p)) : pattern(pat);
            var rt = p.child(SyntaxKind.RET_TYPE);
            if (rt.isPresent()) {
                d = concat(d, text(": "), retType(rt.get()));
            }
            params.add(d);
        }
        return delimited("(", SOFTLINE, plain(params), ")");
    }

    // --- types ---

    private Doc fnType(SyntaxNode n) {
        List<Doc> params = new ArrayList<>();
        Doc result = Doc.NIL;
        boolean afterArrow = false;
        for (SyntaxElement e : meaningful(n)) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.ARROW) {
                afterArrow = true;
            } else if (e instanceof SyntaxNode c && c.kind() == SyntaxKind.RET_TYPE) {
                if (afterArrow) {
                    result = retType(c);
                } else {
                    params.add(retType(c));
                }
            }
        }
        return concat(delimited("(", SOFTLINE, plain(params), ")"), text(" -> "), result);
    }

    private Doc retType(SyntaxNode n) {
        List<Doc> cases = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (isTypeNode(c.kind())) {
                cases.add(typeTerm(c));
            }
        }
        Doc d = cases.isEmpty() ? Doc.NIL
                : chained(cases.get(0), segments("| ", cases.subList(1, cases.size())));
        // `T?` in a core signature, the same mark a field carries
        return n.token(SyntaxKind.QUESTION).isPresent() ? concat(d, text("?")) : d;
    }

    private Doc typeRef(SyntaxNode n) {
        if (n.kind() == SyntaxKind.TUPLE_TYPE) {
            List<Doc> elems = new ArrayList<>();
            for (SyntaxNode c : n.childNodes()) {
                if (isTypeNode(c.kind())) {
                    elems.add(typeTerm(c));
                }
            }
            return delimited("(", SOFTLINE, plain(elems), ")");
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
        List<Doc> typeArgs = new ArrayList<>();
        for (SyntaxNode c : args.get().childNodes()) {
            if (isTypeNode(c.kind())) {
                typeArgs.add(typeTerm(c));
            }
        }
        return concat(name, delimited("<", SOFTLINE, plain(typeArgs), ">"));
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
        if (args.isEmpty()) {
            return text("()");
        }
        SyntaxNode argList = n.child(SyntaxKind.ARG_LIST).orElseThrow();
        List<Member> argDocs = new ArrayList<>();
        for (SyntaxNode a : args) {
            argDocs.add(member(argList, a, expr(a)));
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
            head = expr(left);
        }
        segs.add(new Segment(operatorText(n) + " ", expr(ops.get(1))));
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
        List<Doc> stages = new ArrayList<>();
        Doc head = collectPipe(n, stages);
        return chained(head, segments("|> ", stages));
    }

    /** Flattens a left-nested {@code |>} chain: returns the head doc and fills {@code stages} with each
     * right-hand stage in source order. */
    private Doc collectPipe(SyntaxNode n, List<Doc> stages) {
        List<SyntaxNode> ops = exprChildren(n);
        SyntaxNode left = ops.get(0);
        SyntaxNode right = ops.get(1);
        Doc head;
        if (left.kind() == SyntaxKind.PIPE_EXPR) {
            head = collectPipe(left, stages);
        } else {
            head = expr(left);
        }
        stages.add(expr(right));
        return head;
    }

    private Doc list(SyntaxNode n) {
        List<Member> elems = exprDocs(n);
        if (elems.isEmpty()) {
            return text("[]");
        }
        return delimited("[", SOFTLINE, elems, "]");
    }

    private Doc listComp(SyntaxNode n) {
        List<Member> exprs = exprDocs(n);
        List<Member> guards = exprs.subList(1, exprs.size());
        return concat(text("["), exprs.get(0).doc(), text(" | "),
                group(nest(INDENT, separated(guards))), text("]"));
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
            lines.add(concat(HARDLINE, text("| " + firstIdent(arm) + " -> "), expr(onlyExpr(arm))));
        }
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
            cases.add(concat(HARDLINE, withComments(n, c, matchCase(c)), concat(trailingOf(c))));
        }
        cases.add(endComments(n));
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
            members.add(member(n, c, member));
        }
        if (members.isEmpty()) {
            return concat(text(typeName), text(" {}"));
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
            for (Doc comment : unwritten(commentsBefore(n).getOrDefault(c, List.of()))) {
                lines.add(concat(HARDLINE, comment));
            }
            for (Doc comment : unwritten(leadingDeep(c))) {
                lines.add(concat(HARDLINE, comment));
            }
            Doc d = switch (c.kind()) {
                case LET_STMT -> concat(text("let "), text(firstIdent(c)), writtenType(c),
                        text(" = "), expr(onlyExpr(c)));
                case LET_DESTRUCTURE -> concat(text("let "), pattern(patternChild(c)),
                        text(" = "), expr(onlyExpr(c)));
                case GUARD_STMT -> guardStmt(c);
                default -> expr(c);   // the result expression
            };
            lines.add(concat(HARDLINE, d, concat(trailingOf(c))));
        }
        lines.add(endComments(n));
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

    // --- comments / blank lines ---

    /**
     * A member with the comments written above it in front of it, each on its own line.
     *
     * <p>Where a comment lands in the tree is the parser's business and it is not uniform: a comment
     * above a record-literal field becomes that field's own leading trivia, while one above a match
     * arm becomes a child of the enclosing {@code MATCH_EXPR}, sitting between the scrutinee and the
     * first arm. Asking each member for its leading trivia therefore finds some comments and not
     * others — which is why a comment survived in three constructs and disappeared in eight.
     *
     * <p>So the question is asked of the parent instead: walk its children in document order and the
     * comments fall between the members they were written above, wherever the parser attached them.
     * A member's own leading trivia is added to that, since the two are disjoint — a token belongs to
     * one node.
     *
     * <p>The {@link Doc#HARDLINE} after each comment forces the enclosing group to break. That is not
     * a preference: a {@code //} on a line the group had collapsed would swallow everything after it.
     */
    private Doc withComments(SyntaxNode parent, SyntaxNode member, Doc d) {
        List<SyntaxToken> comments = new ArrayList<>(commentsBefore(parent).getOrDefault(member, List.of()));
        comments.addAll(leadingDeep(member));
        List<Doc> parts = new ArrayList<>();
        for (Doc comment : unwritten(comments)) {
            parts.add(concat(comment, HARDLINE));
        }
        if (parts.isEmpty()) {
            return d;
        }
        parts.add(d);
        return concat(parts);
    }

    /**
     * The comments at the front of a member's own text. {@link #leading} reads only the node's direct
     * children and stops at its first child node, but a parser may put the member's first token a
     * level or two down — an {@code exposing} entry's name is a {@code QUALIFIED_NAME}, and the
     * comment above the entry becomes *that* node's leading trivia. What is written above a member is
     * at the front of its text however deep the front is, so the walk follows the leftmost spine.
     */
    private List<SyntaxToken> leadingDeep(SyntaxNode member) {
        List<SyntaxToken> comments = new ArrayList<>();
        for (SyntaxElement e : member.children()) {
            if (e instanceof SyntaxToken t) {
                if (t.kind() == SyntaxKind.WHITESPACE) {
                    continue;
                }
                if (t.kind() == SyntaxKind.LINE_COMMENT) {
                    comments.add(t);
                    continue;
                }
                break;                      // a real token: the front of the text is here
            }
            if (e instanceof SyntaxNode first) {
                comments.addAll(leadingDeep(first));
                break;                      // only the leftmost child is the front
            }
        }
        return comments;
    }

    /**
     * A parent's comments, by the member each run was written above. {@link #atEnd} is the run after
     * the last member: it was written above nothing, and a walk that only hands a run to the next
     * member it meets never hands that one to anybody. Dropping it is how a comment written at the
     * end of a list disappeared, so it is kept apart rather than left in the walk's state.
     */
    private record ParentComments(Map<SyntaxNode, List<SyntaxToken>> above, List<SyntaxToken> atEnd) {}

    /** Each of {@code parent}'s child nodes against the comment lines written above it — the comments
     * that sit in the parent's own child list rather than on the member. */
    private Map<SyntaxNode, List<SyntaxToken>> commentsBefore(SyntaxNode parent) {
        return comments(parent).above();
    }

    private ParentComments comments(SyntaxNode parent) {
        return commentsByParent.computeIfAbsent(parent, Formatter::scanComments);
    }

    private static ParentComments scanComments(SyntaxNode parent) {
        Map<SyntaxNode, List<SyntaxToken>> above = new IdentityHashMap<>();
        List<SyntaxToken> pending = new ArrayList<>();
        for (SyntaxElement e : parent.children()) {
            if (e instanceof SyntaxToken t) {
                if (t.kind() == SyntaxKind.LINE_COMMENT) {
                    pending.add(t);
                }
            } else if (e instanceof SyntaxNode n && !pending.isEmpty()) {
                above.put(n, List.copyOf(pending));
                pending.clear();
            }
        }
        return new ParentComments(above, List.copyOf(pending));
    }

    /** The comments of {@code run} that have not been written yet, one document each. A comment is
     * reachable from a parent's child list and from the front of a member's own subtree, so which
     * ones are already written is remembered rather than derived. */
    private List<Doc> unwritten(List<SyntaxToken> run) {
        List<Doc> out = new ArrayList<>();
        for (SyntaxToken c : run) {
            if (consumedComments.add(c.start())) {
                out.add(text(c.text().stripTrailing()));
            }
        }
        return out;
    }

    /** The comments written after {@code parent}'s last member, each opening a line of its own. They
     * stay inside the construct, under the member they were written under. */
    private Doc endComments(SyntaxNode parent) {
        List<Doc> parts = new ArrayList<>();
        for (Doc c : unwritten(comments(parent).atEnd())) {
            parts.add(concat(HARDLINE, c));
        }
        return concat(parts);
    }

    /** {@code members} with {@code parent}'s end comments under the last of them — for a construct
     * whose members are joined rather than written a line at a time, where there is no line to add
     * one to except the last member's own document. */
    private List<Member> withEndComments(SyntaxNode parent, List<Member> members) {
        List<Doc> lines = unwritten(comments(parent).atEnd());
        if (lines.isEmpty() || members.isEmpty()) {
            return members;
        }
        List<Member> out = new ArrayList<>(members);
        Member last = out.get(out.size() - 1);
        Doc doc = last.doc();
        for (Doc c : lines) {
            doc = concat(doc, HARDLINE, c);
        }
        out.set(out.size() - 1, new Member(doc, last.trailing()));
        return out;
    }

    /** A member with the comments written above its line in front of it, and the one written at the
     * end of that line kept apart, since what the enclosing construct writes between this member and
     * the next goes between them. */
    private Member member(SyntaxNode parent, SyntaxNode node, Doc d) {
        return new Member(withComments(parent, node, d), concat(trailingOf(node)));
    }

    /**
     * Every comment written after code on the same line, by the construct that code ends. Whether a
     * comment was written above a line or at the end of one is in the tree — the whitespace before a
     * comment on its own line carries the newline that ended the line before it, and the whitespace
     * before a trailing comment does not — so this reads it rather than guessing from position.
     */
    private static Map<SyntaxNode, List<SyntaxToken>> scanTrailing(SyntaxNode file) {
        Map<SyntaxNode, List<SyntaxToken>> out = new IdentityHashMap<>();
        List<SyntaxToken> code = new ArrayList<>();   // the tokens that were not trivia
        boolean lineEnded = true;            // nothing precedes the first token on its line
        for (SyntaxToken t : tokens(file)) {
            if (t.kind() == SyntaxKind.WHITESPACE) {
                lineEnded |= t.text().indexOf('\n') >= 0;
            } else if (t.kind() == SyntaxKind.LINE_COMMENT) {
                // a comma is the enclosing construct's, so a comment after one was written about
                // the member the comma closed rather than about the comma
                int i = code.size() - 1;
                while (i >= 0 && code.get(i).kind() == SyntaxKind.COMMA) {
                    i--;
                }
                if (!lineEnded && i >= 0) {
                    out.computeIfAbsent(owner(code.get(i)), _ -> new ArrayList<>()).add(t);
                }
                lineEnded = true;            // a line comment runs to the end of its line
            } else {
                code.add(t);
                lineEnded = false;
            }
        }
        return out;
    }

    /**
     * The construct a comment written after {@code code} was written about: the outermost one that
     * ends where {@code code} does. {@code data D = A | B   // c} is about the declaration and not
     * about {@code B}, and {@code , f: T   // c} is about the field and not about the block, and the
     * two are the same rule — what ends on that line is what the line was about.
     */
    private static SyntaxNode owner(SyntaxToken code) {
        SyntaxNode node = code.parent();
        while (node.parent() != null && node.parent().parent() != null
                && node.parent().end() == code.end()) {
            node = node.parent();
        }
        return node;
    }

    /** {@code n}'s trailing comments, marked consumed. Empty where it has none, or where they have
     * been written already. */
    private List<Doc> trailingOf(SyntaxNode n) {
        List<Doc> out = new ArrayList<>();
        for (SyntaxToken c : trailing.getOrDefault(n, List.of())) {
            if (consumedComments.add(c.start())) {
                out.add(Doc.trailing(c.text().stripTrailing()));
            }
        }
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

    private List<SyntaxToken> trailingComments(SyntaxNode file) {
        List<SyntaxToken> out = new ArrayList<>();
        int lastNode = -1;
        List<SyntaxElement> es = file.children();
        for (int i = 0; i < es.size(); i++) {
            if (es.get(i) instanceof SyntaxNode) {
                lastNode = i;
            }
        }
        for (int i = lastNode + 1; i < es.size(); i++) {
            if (es.get(i) instanceof SyntaxToken t && t.kind() == SyntaxKind.LINE_COMMENT) {
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
            out.add(member(n, c, expr(c)));
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
