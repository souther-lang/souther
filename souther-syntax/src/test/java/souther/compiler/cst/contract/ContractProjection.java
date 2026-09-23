package souther.compiler.cst.contract;

import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * How this compiler's concrete syntax tree reads as the contract syntax tree.
 *
 * <p>This is the compiler's claim about itself: that the tree {@code CstParser} builds is, node for
 * node, the tree the grammar says the source is. The grammar does not know this class and the
 * compiler's own code does not use it — it sits between the two only so the corpus can hold one to
 * the other.
 *
 * <p>Every {@link SyntaxKind} is answered, with no default, so a kind added to the parser does not
 * compile here until somebody says what it is in the contract: a node, the tokens under it, or
 * nothing. The CST writes some names flat where the grammar has a node — a dotted name as the
 * identifiers and dots it is made of, a match case's pattern as the tokens it is spelled with — and
 * those are gathered into the grammar's nodes here, where the difference between the two trees is
 * this class's business and no one else's.
 */
final class ContractProjection {

    private ContractProjection() {}

    /** The contract tree {@code root}, the parse of a whole source, is. */
    static ContractTree of(SyntaxNode root) {
        List<ContractTree> read = project(root);
        if (read.size() != 1) {
            throw new IllegalStateException("a source file reads as " + read.size() + " nodes");
        }
        return read.getFirst();
    }

    private static List<ContractTree> project(SyntaxElement element) {
        return switch (element.kind()) {
            case WHITESPACE, LINE_COMMENT, EOF, CONTEXTUAL_KW,
                 MODULE_KW, IMPORT_KW, EXPOSING_KW, DATA_KW, INVARIANT_KW, ENSURES_KW, AS_KW, LET_KW,
                 GUARD_KW, ELSE_KW, IF_KW, THEN_KW, BEHAVIOR_KW, DEPENDS_KW, CONSTRUCTS_KW,
                 MATCH_KW, WITH_KW, UNREACHABLE_KW,
                 LBRACE, RBRACE, LPAREN, RPAREN, LBRACKET, RBRACKET, COLON, COMMA, DOT, SPREAD,
                 ASSIGN, PIPE, ARROW, PIPEFWD, VPIPE, QUESTION, PLUSPLUS,
                 EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS, STAR, SLASH -> List.of();

            case IDENT, INT_LIT, DECIMAL_LIT, STRING_LIT, TYPEVAR ->
                    leaf(tokenClass(element.kind()).orElseThrow());
            case TRUE_KW, FALSE_KW -> leaf("boolean-literal");
            case UNDERSCORE -> leaf("discard");
            case UNANSWERED -> leaf("answer-owed");
            case ERROR_TOKEN -> leaf("ERROR");

            case SOURCE_FILE -> node("source-file", element);
            case MODULE_HEADER -> node("module-header", element);
            case EXPOSING_CLAUSE -> node("exposing-clause", element);
            case EXPOSED_ENTRY -> node("exposed-entry", element);
            case IMPORT_DECL -> node("import-declaration", element);
            case IMPORT_ALIAS -> node("import-alias", element);
            case NAME_LIST -> node("name-list", element);
            case QUALIFIED_NAME -> node("qualified-name", element);

            case DATA_DEF -> node("data-declaration", element);
            case PRODUCT_BODY -> node("product-body", element);
            case FIELD -> field(element);
            case SPREAD_MEMBER -> node(parentKind(element) == SyntaxKind.PRODUCT_BODY
                    ? "field-spread" : "record-spread", element);
            case SUM_BODY -> node("sum-body", element);
            case NEWTYPE_BODY -> List.of(new ContractTree("newtype-body",
                    wholeType(meaningful(element))));
            case INVARIANT_CLAUSE -> node("invariant-clause", element);

            case BEHAVIOR_DEF -> node("behavior-declaration", element);
            case BEHAVIOR_SIG -> node("behavior-signature", element);
            case PIPE_BEHAVIOR -> node("composition", element);
            case STAGE -> qualifiedNames(meaningful(element));
            case PARAM_LIST -> node("parameter-list", element);
            case PARAM -> node("parameter", element);
            case CONSTRUCTS_CLAUSE -> List.of(new ContractTree("constructs-clause",
                    qualifiedNames(meaningful(element))));
            case DEPENDS_CLAUSE -> List.of(new ContractTree("depends-clause",
                    qualifiedNames(meaningful(element))));
            case ENSURES_CLAUSE -> node("ensures-clause", element);
            case ENSURES_ARM -> node("ensures-arm", element);

            case FN_DEF -> node("let-definition", element);
            case FN_PARAM_LIST -> node("function-parameter-list", element);
            case FN_PARAM -> node("function-parameter", element);
            case INTRINSIC_BODY -> node("intrinsic-body", element);
            case PARTIAL_MODIFIER -> node("partial-modifier", element);
            case PRIVATE_MODIFIER -> node("private-modifier", element);

            case EXAMPLE_DEF -> node("example-declaration", element);
            case EXAMPLE_ROW -> node("example-row", element);
            case EXAMPLES_FILE_HEADER -> node("examples-file-header", element);
            case WITH_CLAUSE -> node("with-clause", element);
            case WITH_BINDING -> List.of(new ContractTree("with-binding",
                    qualifiedNames(meaningful(element))));
            case FAKE_DEF -> List.of(new ContractTree("fake-declaration",
                    qualifiedNames(meaningful(element))));
            case FAKE_ROW -> node("fake-row", element);

            case RET_TYPE -> wholeType(meaningful(element));
            case TYPE_REF -> List.of(new ContractTree("type-reference",
                    qualifiedNames(meaningful(element))));
            case TYPE_ARGS -> node("type-arguments", element);
            case TUPLE_TYPE -> tupleType(element);
            case FN_TYPE -> node("function-type", element);

            case LET_STMT -> node("let-binding", element);
            case LET_DESTRUCTURE -> node("let-destructuring", element);
            case GUARD_STMT -> List.of(new ContractTree("guard-statement",
                    asBindings(meaningful(element))));

            case PATTERN_NAME -> node("pattern-name", element);
            case PATTERN_TUPLE -> node("tuple-pattern", element);
            case PATTERN_CTOR -> List.of(new ContractTree("constructor-pattern",
                    qualifiedNames(meaningful(element))));
            case PATTERN_RECORD -> node("record-pattern", element);
            case PATTERN_FIELD -> node("field-pattern", element);

            case BLOCK_EXPR -> node("block", element);
            case PIPE_EXPR -> node("pipe-expression", element);
            case BINARY_EXPR -> node(binaryOperation(element), element);
            case UNARY_EXPR -> node("negation", element);
            case APPLY_EXPR -> node("application", element);
            case ARG_LIST -> node("argument-list", element);
            case FIELD_ACCESS -> node("field-access", element);
            case VAR_EXPR -> node("variable", element);
            case LITERAL_EXPR -> children(element);
            case PAREN_EXPR -> node("parenthesized-expression", element);
            case TUPLE_EXPR -> node("tuple-expression", element);
            case LIST_EXPR -> node("list-expression", element);
            case LIST_COMP -> node("list-comprehension", element);
            case IF_EXPR -> List.of(new ContractTree("if-expression", asBindings(meaningful(element))));
            case ELSE_ARMS -> node("else-arms", element);
            case ELSE_ARM -> node("else-arm", element);
            case MATCH_EXPR -> node("match-expression", element);
            case MATCH_CASE -> List.of(new ContractTree("match-case", matchCase(meaningful(element))));
            case LAMBDA_EXPR -> List.of(new ContractTree("lambda", lambda(meaningful(element))));
            case FIELD_GETTER -> node("field-getter", element);
            case NEW_DATA_EXPR -> List.of(new ContractTree("construction",
                    qualifiedNames(meaningful(element))));
            case FIELD_INIT -> node("field-initializer", element);
            case UNREACHABLE_EXPR -> node("unreachable-expression", element);
        };
    }

    /**
     * The open token class of the contract a token of {@code kind} is, if it is one: a token whose
     * text the source supplies. A fixed spelling is not a class, and neither is a node, the end of
     * input, the fragment a lexical error covers, or a contextual word the parser read as one —
     * that is a spelling of the name it lexed as.
     *
     * <p>Written with no default, so a kind added to the lexer does not compile here until it is
     * said to be one of the contract's token classes or none of them, which is what lets the
     * vocabulary's lists be compared with the compiler's rather than with themselves.
     */
    static Optional<String> tokenClass(SyntaxKind kind) {
        return Optional.ofNullable(switch (kind) {
            case WHITESPACE -> "whitespace";
            case LINE_COMMENT -> "line-comment";
            case IDENT -> "identifier";
            case INT_LIT -> "integer-literal";
            case DECIMAL_LIT -> "decimal-literal";
            case STRING_LIT -> "string-literal";
            case TYPEVAR -> "type-variable";
            case CONTEXTUAL_KW, EOF, ERROR_TOKEN,
                 MODULE_KW, IMPORT_KW, EXPOSING_KW, DATA_KW, INVARIANT_KW, ENSURES_KW, AS_KW, LET_KW,
                 GUARD_KW, ELSE_KW, TRUE_KW, FALSE_KW, IF_KW, THEN_KW, BEHAVIOR_KW, DEPENDS_KW,
                 CONSTRUCTS_KW, MATCH_KW, WITH_KW, UNREACHABLE_KW,
                 LBRACE, RBRACE, LPAREN, RPAREN, LBRACKET, RBRACKET, COLON, COMMA, DOT, SPREAD,
                 ASSIGN, PIPE, ARROW, PIPEFWD, VPIPE, QUESTION, PLUSPLUS, UNDERSCORE, UNANSWERED,
                 EQ, NE, LT, LE, GT, GE, AND, OR, PLUS, MINUS, STAR, SLASH,
                 SOURCE_FILE, MODULE_HEADER, EXPOSING_CLAUSE, EXPOSED_ENTRY, IMPORT_DECL,
                 IMPORT_ALIAS, NAME_LIST, QUALIFIED_NAME,
                 DATA_DEF, PRODUCT_BODY, FIELD, SPREAD_MEMBER, SUM_BODY, NEWTYPE_BODY,
                 INVARIANT_CLAUSE,
                 BEHAVIOR_DEF, BEHAVIOR_SIG, PIPE_BEHAVIOR, PARAM_LIST, PARAM, CONSTRUCTS_CLAUSE,
                 DEPENDS_CLAUSE, ENSURES_CLAUSE, ENSURES_ARM, STAGE,
                 FN_DEF, FN_PARAM_LIST, FN_PARAM, INTRINSIC_BODY, PARTIAL_MODIFIER,
                 PRIVATE_MODIFIER,
                 EXAMPLE_DEF, EXAMPLE_ROW, EXAMPLES_FILE_HEADER, WITH_CLAUSE, WITH_BINDING,
                 FAKE_DEF, FAKE_ROW,
                 RET_TYPE, TYPE_REF, TYPE_ARGS, TUPLE_TYPE, FN_TYPE,
                 LET_STMT, LET_DESTRUCTURE, GUARD_STMT,
                 PATTERN_NAME, PATTERN_TUPLE, PATTERN_CTOR, PATTERN_RECORD, PATTERN_FIELD,
                 BLOCK_EXPR, PIPE_EXPR, BINARY_EXPR, UNARY_EXPR, APPLY_EXPR, ARG_LIST, FIELD_ACCESS,
                 VAR_EXPR, LITERAL_EXPR, PAREN_EXPR, TUPLE_EXPR, LIST_EXPR, LIST_COMP, IF_EXPR,
                 ELSE_ARMS, ELSE_ARM, MATCH_EXPR, MATCH_CASE, LAMBDA_EXPR, FIELD_GETTER,
                 NEW_DATA_EXPR, FIELD_INIT, UNREACHABLE_EXPR -> null;
        });
    }

    private static List<ContractTree> leaf(String id) {
        return List.of(ContractTree.leaf(id));
    }

    private static List<ContractTree> node(String id, SyntaxElement element) {
        return List.of(new ContractTree(id, children(element)));
    }

    private static List<ContractTree> children(SyntaxElement element) {
        List<ContractTree> out = new ArrayList<>();
        for (SyntaxElement child : meaningful(element)) {
            out.addAll(project(child));
        }
        return out;
    }

    /** The children a reader of the contract sees: no whitespace, no comment, no end of input. */
    private static List<SyntaxElement> meaningful(SyntaxElement element) {
        if (!(element instanceof SyntaxNode node)) {
            return List.of();
        }
        return node.children().stream()
                .filter(child -> !child.kind().isTrivia() && child.kind() != SyntaxKind.EOF)
                .toList();
    }

    private static SyntaxKind parentKind(SyntaxElement element) {
        return ((SyntaxNode) element).parent().kind();
    }

    /**
     * The children, with every run of {@code name(.name)*} gathered into a {@code qualified-name}.
     * Only a node the grammar writes a qualified name in is read this way.
     */
    private static List<ContractTree> qualifiedNames(List<SyntaxElement> children) {
        List<ContractTree> out = new ArrayList<>();
        int i = 0;
        while (i < children.size()) {
            if (children.get(i).kind() == SyntaxKind.IDENT) {
                i = qualifiedName(children, i, out);
            } else {
                out.addAll(project(children.get(i)));
                i++;
            }
        }
        return out;
    }

    /** Reads one dotted name from {@code i} into {@code out}, and answers where it ends. */
    private static int qualifiedName(List<SyntaxElement> children, int i, List<ContractTree> out) {
        List<ContractTree> parts = new ArrayList<>();
        parts.add(ContractTree.leaf("identifier"));
        int at = i + 1;
        while (at + 1 < children.size() && children.get(at).kind() == SyntaxKind.DOT
                && children.get(at + 1).kind() == SyntaxKind.IDENT) {
            parts.add(ContractTree.leaf("identifier"));
            at += 2;
        }
        out.add(new ContractTree("qualified-name", parts));
        return at;
    }

    /** The children, with each {@code as x} gathered into an {@code as-binding}. */
    private static List<ContractTree> asBindings(List<SyntaxElement> children) {
        List<ContractTree> out = new ArrayList<>();
        for (int i = 0; i < children.size(); i++) {
            if (children.get(i).kind() == SyntaxKind.AS_KW && i + 1 < children.size()
                    && children.get(i + 1).kind() == SyntaxKind.IDENT) {
                out.add(new ContractTree("as-binding", List.of(ContractTree.leaf("identifier"))));
                i++;
            } else {
                out.addAll(project(children.get(i)));
            }
        }
        return out;
    }

    /**
     * A type written where a whole type is read: its members, a {@code |} between two of them making
     * a {@code union-type}, and a {@code ?} after them making what they are an {@code optional-type}.
     */
    private static List<ContractTree> wholeType(List<SyntaxElement> children) {
        List<ContractTree> members = new ArrayList<>();
        boolean union = false;
        boolean optional = false;
        for (SyntaxElement child : children) {
            switch (child.kind()) {
                case PIPE -> union = true;
                case QUESTION -> optional = true;
                default -> members.addAll(project(child));
            }
        }
        List<ContractTree> core = union ? List.of(new ContractTree("union-type", members)) : members;
        return optional ? List.of(new ContractTree("optional-type", core)) : core;
    }

    /** A data field: its name, then its type as a whole type is read, which a field never unites. */
    private static List<ContractTree> field(SyntaxElement element) {
        List<SyntaxElement> children = meaningful(element);
        List<ContractTree> out = new ArrayList<>();
        int colon = 0;
        while (colon < children.size() && children.get(colon).kind() != SyntaxKind.COLON) {
            out.addAll(project(children.get(colon)));
            colon++;
        }
        out.addAll(wholeType(children.subList(Math.min(colon + 1, children.size()), children.size())));
        return List.of(new ContractTree("field", out));
    }

    /** {@code (A)} groups one type; {@code ()}, {@code (A,)} and {@code (A, B)} are tuples. */
    private static List<ContractTree> tupleType(SyntaxElement element) {
        List<SyntaxElement> children = meaningful(element);
        boolean comma = children.stream().anyMatch(child -> child.kind() == SyntaxKind.COMMA);
        List<ContractTree> members = children(element);
        return List.of(new ContractTree(members.size() == 1 && !comma
                ? "parenthesized-type" : "tuple-type", members));
    }

    private static String binaryOperation(SyntaxElement element) {
        for (SyntaxElement child : meaningful(element)) {
            switch (child.kind()) {
                case OR -> {
                    return "or-expression";
                }
                case AND -> {
                    return "and-expression";
                }
                case EQ, NE, LT, LE, GT, GE -> {
                    return "comparison";
                }
                case PLUS, MINUS, PLUSPLUS -> {
                    return "additive-expression";
                }
                case STAR, SLASH -> {
                    return "multiplicative-expression";
                }
                default -> {
                }
            }
        }
        throw new IllegalStateException("a binary expression with no operator: " + element);
    }

    /** {@code x -> e} names its parameter bare; {@code (p, ...) -> e} writes patterns. */
    private static List<ContractTree> lambda(List<SyntaxElement> children) {
        List<ContractTree> out = new ArrayList<>();
        boolean bare = !children.isEmpty() && children.getFirst().kind() == SyntaxKind.PATTERN_NAME;
        for (int i = 0; i < children.size(); i++) {
            if (bare && i == 0) {
                out.addAll(children(children.getFirst()));
            } else {
                out.addAll(project(children.get(i)));
            }
        }
        return out;
    }

    /**
     * A match case, which the CST keeps as the tokens its pattern is spelled with: the case names,
     * then an unwrapping {@code (X(...))} or a positional binding, then the fields it opens, then
     * {@code as x}, then the body.
     */
    private static List<ContractTree> matchCase(List<SyntaxElement> children) {
        List<ContractTree> out = new ArrayList<>();
        int i = qualifiedName(children, 0, out);
        while (i < children.size() && children.get(i).kind() == SyntaxKind.PIPE) {
            i = qualifiedName(children, i + 1, out);
        }
        if (i < children.size() && children.get(i).kind() == SyntaxKind.LPAREN) {
            i = caseUnwrap(children, i, out);
        } else if (i < children.size() && children.get(i).kind() == SyntaxKind.IDENT) {
            out.add(new ContractTree("positional-binding", List.of(ContractTree.leaf("identifier"))));
            i++;
        }
        if (i < children.size() && children.get(i).kind() == SyntaxKind.LBRACE) {
            List<ContractTree> fields = new ArrayList<>();
            i++;
            while (i < children.size() && children.get(i).kind() != SyntaxKind.RBRACE) {
                if (children.get(i).kind() == SyntaxKind.IDENT) {
                    List<ContractTree> names = new ArrayList<>();
                    names.add(ContractTree.leaf("identifier"));
                    if (i + 2 < children.size() && children.get(i + 1).kind() == SyntaxKind.ASSIGN) {
                        names.add(ContractTree.leaf("identifier"));
                        i += 2;
                    }
                    fields.add(new ContractTree("field-pattern", names));
                }
                i++;
            }
            out.add(new ContractTree("record-pattern", fields));
            i++;
        }
        out.addAll(asBindings(children.subList(Math.min(i, children.size()), children.size())));
        return out;
    }

    /** {@code ( X [ (...) ] )}, from the {@code (} at {@code i}; answers where it ends. */
    private static int caseUnwrap(List<SyntaxElement> children, int i, List<ContractTree> out) {
        List<ContractTree> inside = new ArrayList<>();
        int at = qualifiedName(children, i + 1, inside);
        if (at < children.size() && children.get(at).kind() == SyntaxKind.LPAREN) {
            at = caseUnwrap(children, at, inside);
        }
        out.add(new ContractTree("case-unwrap", inside));
        return at + 1;
    }
}
