package souther.lsp.analysis;

import souther.compiler.check.SpecImplementation;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.TopLevelForm;
import souther.compiler.fmt.Skeleton;

import java.util.ArrayList;
import java.util.List;

/**
 * The declarations an editor offers to write, as tokens.
 *
 * <p>Nothing here spells a keyword or a bracket. A form's own words come from {@link TopLevelForm},
 * which is what recognises them, and everything else from {@link SyntaxKind#fixedSpelling()}, which
 * is what the language writes them as. What is left to choose is which of the forms the grammar
 * allows to offer — a {@code behavior} may be written as a signature or as a composition, and only
 * one of those can be offered — and that choice is this server's, since it is about what helps
 * someone writing rather than about what the language admits.
 *
 * <p>Where a declaration can be read, the skeleton is built from it and holds a hole exactly where
 * the compiler settles nothing. Where one cannot, the skeleton states what a form is and no more:
 * three parameter holes because behaviors often take three would be this server inventing a
 * signature it did not read.
 */
final class DeclarationSkeletons {

    private DeclarationSkeletons() {}

    /** What a hole stands in with until the author replaces it. */
    private static final String A_NAME = "name";
    private static final String A_PARAMETER = "param";
    private static final String A_BODY = "body";
    private static final String A_TYPE = "Type";
    private static final String AN_ARGUMENT = "arg";
    private static final String AN_EXPECTED = "expected";
    private static final String A_VALUE = "value";

    /**
     * The {@code let} implementing a behavior: its name, the parameters it is required to take, and
     * a body.
     *
     * <p>An input is a hole standing in with the behavior's own spelling, which is a suggestion; an
     * injected parameter is written out, because its name is the behavior it injects and any other
     * spelling is refused.
     */
    static List<Skeleton.Part> implementing(String behavior,
                                            List<SpecImplementation.Parameter> parameters) {
        List<Skeleton.Part> parts = new ArrayList<>();
        parts.add(literal(starterOf(TopLevelForm.FN), name(behavior), spelt(SyntaxKind.LPAREN)));
        for (int i = 0; i < parameters.size(); i++) {
            if (i > 0) {
                parts.add(literal(spelt(SyntaxKind.COMMA)));
            }
            switch (parameters.get(i)) {
                case SpecImplementation.Parameter.Input input ->
                        parts.add(hole(Skeleton.Category.IDENTIFIER, input.nameSuggestion()));
                case SpecImplementation.Parameter.Injected injected ->
                        parts.add(literal(name(injected.name())));
                // A dependency naming nothing settles no parameter to write. Nothing is offered for
                // a behavior holding one, so this is unreachable through what offers a skeleton.
                case SpecImplementation.Parameter.Unanswered _ ->
                        parts.add(hole(Skeleton.Category.IDENTIFIER, A_PARAMETER));
            }
        }
        parts.add(literal(spelt(SyntaxKind.RPAREN), spelt(SyntaxKind.ASSIGN)));
        parts.add(hole(Skeleton.Category.EXPRESSION, A_BODY));
        return List.copyOf(parts);
    }

    /**
     * An {@code example} for a behavior: one row, stating as many arguments as the behavior takes
     * inputs, supplying what nothing already stands in for, and expecting something.
     *
     * <p>The row states the inputs alone. What a behavior depends on is not passed to it — a row
     * supplies that through {@code with}, or a {@code fake} table beside the rows does — so a row
     * with a place for every parameter would have one place too many for each dependency.
     */
    static List<Skeleton.Part> exampleFor(String target,
                                          List<SpecImplementation.Parameter> parameters,
                                          List<String> unsupplied) {
        List<Skeleton.Part> parts = new ArrayList<>();
        parts.add(literal(starterOf(TopLevelForm.EXAMPLE), name(target), spelt(SyntaxKind.PIPE),
                spelt(SyntaxKind.LPAREN)));
        int written = 0;
        for (SpecImplementation.Parameter parameter : parameters) {
            if (parameter instanceof SpecImplementation.Parameter.Input input) {
                if (written > 0) {
                    parts.add(literal(spelt(SyntaxKind.COMMA)));
                }
                parts.add(hole(Skeleton.Category.EXPRESSION, input.nameSuggestion()));
                written++;
            }
        }
        parts.add(literal(spelt(SyntaxKind.RPAREN)));
        for (int i = 0; i < unsupplied.size(); i++) {
            parts.add(literal(i == 0 ? spelt(SyntaxKind.WITH_KW) : spelt(SyntaxKind.COMMA),
                    name(unsupplied.get(i)), spelt(SyntaxKind.ASSIGN)));
            parts.add(hole(Skeleton.Category.EXPRESSION, A_VALUE));
        }
        parts.add(literal(spelt(SyntaxKind.ARROW)));
        parts.add(hole(Skeleton.Category.EXPRESSION, AN_EXPECTED));
        return List.copyOf(parts);
    }

    /**
     * The skeleton for a form where no declaration was read, which states what the form is and
     * nothing it was not told.
     *
     * <p>A switch over the forms, so a form added to the catalog does not compile until there is
     * something to offer for it.
     */
    static List<Skeleton.Part> fixed(TopLevelForm form) {
        return switch (form) {
            case MODULE_HEADER -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME));
            case EXAMPLES_FILE_HEADER -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME));
            case IMPORT -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.LPAREN)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.RPAREN)));
            case DATA -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_TYPE),
                    literal(spelt(SyntaxKind.ASSIGN), spelt(SyntaxKind.LBRACE)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.COLON)),
                    hole(Skeleton.Category.IDENTIFIER, A_TYPE),
                    literal(spelt(SyntaxKind.RBRACE)));
            case BEHAVIOR -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.COLON), spelt(SyntaxKind.LPAREN)),
                    hole(Skeleton.Category.IDENTIFIER, A_PARAMETER),
                    literal(spelt(SyntaxKind.COLON)),
                    hole(Skeleton.Category.IDENTIFIER, A_TYPE),
                    literal(spelt(SyntaxKind.RPAREN), spelt(SyntaxKind.ARROW)),
                    hole(Skeleton.Category.IDENTIFIER, A_TYPE));
            case FN -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.LPAREN)),
                    hole(Skeleton.Category.IDENTIFIER, A_PARAMETER),
                    literal(spelt(SyntaxKind.RPAREN), spelt(SyntaxKind.ASSIGN)),
                    hole(Skeleton.Category.EXPRESSION, A_BODY));
            case EXAMPLE -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.PIPE), spelt(SyntaxKind.LPAREN)),
                    hole(Skeleton.Category.EXPRESSION, AN_ARGUMENT),
                    literal(spelt(SyntaxKind.RPAREN), spelt(SyntaxKind.ARROW)),
                    hole(Skeleton.Category.EXPRESSION, AN_EXPECTED));
            case FAKE -> List.of(
                    literal(starterOf(form)),
                    hole(Skeleton.Category.IDENTIFIER, A_NAME),
                    literal(spelt(SyntaxKind.PIPE), spelt(SyntaxKind.LPAREN)),
                    hole(Skeleton.Category.EXPRESSION, AN_ARGUMENT),
                    literal(spelt(SyntaxKind.RPAREN), spelt(SyntaxKind.ARROW)),
                    hole(Skeleton.Category.EXPRESSION, A_VALUE));
        };
    }

    /** The words a form is opened with, as tokens to write. */
    private static List<Skeleton.Word> starterOf(TopLevelForm form) {
        return form.words().stream()
                .map(word -> new Skeleton.Word(word.kind(), word.spelling()))
                .toList();
    }

    /** A token the language spells for itself. */
    private static Skeleton.Word spelt(SyntaxKind kind) {
        return new Skeleton.Word(kind, kind.fixedSpelling().orElseThrow(
                () -> new IllegalArgumentException(kind + " does not spell itself")));
    }

    private static Skeleton.Word name(String spelling) {
        return new Skeleton.Word(SyntaxKind.IDENT, spelling);
    }

    private static Skeleton.Part literal(Skeleton.Word... words) {
        return new Skeleton.Part.Literal(List.of(words));
    }

    private static Skeleton.Part literal(List<Skeleton.Word> opening, Skeleton.Word... rest) {
        List<Skeleton.Word> words = new ArrayList<>(opening);
        words.addAll(List.of(rest));
        return new Skeleton.Part.Literal(List.copyOf(words));
    }

    private static Skeleton.Part hole(Skeleton.Category category, String spelling) {
        return new Skeleton.Part.Hole(category, List.of(name(spelling)));
    }
}
