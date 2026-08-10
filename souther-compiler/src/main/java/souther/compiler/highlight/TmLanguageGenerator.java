package souther.compiler.highlight;

import souther.compiler.Prelude;
import souther.compiler.cst.CstLexer;
import souther.compiler.cst.IdentifierAlphabet;
import souther.compiler.editor.EditorSymbols;
import tools.jackson.databind.json.JsonMapper;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

/**
 * Generates a TextMate grammar ({@code souther.tmLanguage.json}) from the language's lexical
 * vocabulary, so the editor highlighting and GitHub Linguist rendering stay in step with the lexer.
 * The keyword list comes from {@link CstLexer#keywords()} — the single source of truth — and a test
 * asserts every keyword is categorised here, so adding one to the lexer forces a grammar update. The
 * symbols come from {@link EditorSymbols}, which the language server reads too, so what an editor
 * paints as an operator is decided once for both. A name's characters come from
 * {@link IdentifierAlphabet} the same way, written out as character classes: an editor's engine
 * cannot ask the compiler and has no Unicode property for the answer, so it is given the answer
 * rather than an ASCII pattern standing in for it.
 *
 * <p>A regex grammar deliberately stops at what the token stream can classify (keywords, operators,
 * literals, comments, stdlib qualifiers). Distinguishing a type name from a value — which in Souther
 * are Japanese identifiers, not capitalised — is left to the LSP's semantic tokens.
 *
 * <p>Regenerate the committed grammar with:
 * <pre>{@code
 * mvn -q -pl souther-compiler exec:java -Dexec.mainClass=souther.compiler.highlight.TmLanguageGenerator
 * }</pre>
 * A release attaches the result so the VS Code extension (souther-lang/souther-vscode) can fetch it
 * instead of building the compiler.
 */
public final class TmLanguageGenerator {

    /** The generated grammar is committed here, as a resource of this module, so a release can attach
     *  it and the editor extension can pick it up without building the compiler. Relative to the
     *  repository root, which is where {@code mvn exec:java} runs. */
    public static final String COMMITTED =
            "souther-compiler/src/main/resources/souther/compiler/highlight/souther.tmLanguage.json";

    /** The same file as a classpath resource, for reading it back. */
    public static final String RESOURCE = "souther.tmLanguage.json";

    /** Declaration keywords — the top-level shapes. */
    private static final Set<String> DECLARATION =
            Set.of("module", "import", "exposing", "data", "behavior", "let");

    /** Control and clause keywords. */
    private static final Set<String> CONTROL =
            Set.of("if", "then", "else", "match", "with", "guard", "constructs", "depends",
                    "as", "invariant", "unreachable");

    /** Boolean literals (scoped as language constants, not keywords). */
    private static final Set<String> BOOLEANS = Set.of("true", "false");

    /** The standard-library qualifiers, taken from {@link Prelude#qualifiers()} (the single source of
     *  truth) and sorted for a stable grammar; highlighted before a dot. Adding a module to the prelude
     *  extends this automatically — no separate list to keep in step. */
    private static final List<String> QUALIFIERS =
            Prelude.qualifiers().stream().sorted().toList();

    /** The operators as {@link EditorSymbols} classifies them, spelled by their kinds, longest first
     *  so a prefix ({@code >}) never masks a longer form ({@code >->}). Sorting by length is what
     *  makes that true rather than the order they are written in, since a prefix is shorter than what
     *  it is a prefix of. */
    static final List<String> OPERATORS = EditorSymbols.operators().stream()
            .map(kind -> kind.fixedSpelling().orElseThrow())
            .sorted(Comparator.comparingInt(String::length).reversed()
                    .thenComparing(Comparator.naturalOrder()))
            .toList();

    private TmLanguageGenerator() {
    }

    /** Writes the grammar to the path given as the first argument, defaulting to the committed
     *  resource. */
    public static void main(String[] args) throws Exception {
        Path out = Path.of(args.length > 0 ? args[0] : COMMITTED);
        Files.createDirectories(out.getParent());
        Files.writeString(out, generate());
    }

    /** The grammar as pretty-printed JSON (ending with a newline). */
    public static String generate() {
        Map<String, Object> repository = new LinkedHashMap<>();
        repository.put("comments", match("comment.line.double-slash.souther", "//.*$"));
        repository.put("strings", strings());
        repository.put("decimal", match("constant.numeric.decimal.souther", "\\b[0-9]+(\\.[0-9]+)?m\\b"));
        repository.put("integer", match("constant.numeric.integer.souther", "\\b[0-9]+\\b"));
        repository.put("booleans", match("constant.language.boolean.souther", wordAlternation(BOOLEANS)));
        repository.put("declaration-keywords",
                match("keyword.declaration.souther", wordAlternation(DECLARATION)));
        // `on` is not reserved, so it is not in CONTROL; matched here it is highlighted only where
        // it is the second word of `depends on`, and stays an ordinary name everywhere else.
        repository.put("depends-on", match("keyword.control.souther", "\\bdepends\\s+on\\b"));
        repository.put("control-keywords",
                match("keyword.control.souther", wordAlternation(CONTROL)));
        repository.put("type-variable", match("variable.other.generic.souther",
                "'[" + IdentifierAlphabet.startClass() + "][" + IdentifierAlphabet.continueClass() + "]*"));
        repository.put("qualifiers",
                match("support.class.souther", "\\b(" + String.join("|", QUALIFIERS) + ")\\b(?=\\s*\\.)"));
        repository.put("operators", match("keyword.operator.souther", operatorAlternation()));

        List<Object> patterns = List.of(
                include("#comments"), include("#strings"), include("#decimal"), include("#integer"),
                include("#booleans"), include("#declaration-keywords"), include("#depends-on"),
                include("#control-keywords"),
                include("#type-variable"), include("#qualifiers"), include("#operators"));

        Map<String, Object> grammar = new LinkedHashMap<>();
        grammar.put("$schema",
                "https://raw.githubusercontent.com/martinring/tmlanguage/master/tmlanguage.json");
        grammar.put("name", "Souther");
        grammar.put("scopeName", "source.souther");
        grammar.put("fileTypes", List.of("sou"));
        grammar.put("patterns", patterns);
        grammar.put("repository", repository);

        try {
            return JsonMapper.builder().build()
                    .writerWithDefaultPrettyPrinter().writeValueAsString(grammar) + "\n";
        } catch (Exception e) {
            throw new IllegalStateException("failed to serialise the TextMate grammar", e);
        }
    }

    private static Map<String, Object> match(String scope, String regex) {
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("name", scope);
        m.put("match", regex);
        return m;
    }

    private static Map<String, Object> include(String ref) {
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("include", ref);
        return m;
    }

    /**
     * A string literal, ended by its quote or by the line, whichever comes first — the literal does
     * not span lines, so a missing quote colours one line rather than the rest of the file.
     *
     * <p>The escapes come from {@link CstLexer#escapes()}, and a backslash before anything else is
     * marked as what it is: the compiler refuses it, and an editor that coloured it as an escape
     * would be promising a compile that does not happen.
     */
    private static Map<String, Object> strings() {
        Map<String, Object> escape = new LinkedHashMap<>();
        escape.put("name", "constant.character.escape.souther");
        escape.put("match", "\\\\[" + escapeClass() + "]");
        Map<String, Object> refused = new LinkedHashMap<>();
        refused.put("name", "invalid.illegal.escape.souther");
        refused.put("match", "\\\\.");
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("name", "string.quoted.double.souther");
        m.put("begin", "\"");
        m.put("end", "\"|$");
        m.put("patterns", List.of(escape, refused));
        return m;
    }

    /** The escapes as a character class, sorted for a stable, reproducible file. */
    private static String escapeClass() {
        return new TreeSet<>(CstLexer.escapes()).stream()
                .map(TmLanguageGenerator::regexEscape)
                .collect(Collectors.joining());
    }

    /** A word-boundary alternation over a sorted keyword set (sorted for a stable, reproducible file). */
    private static String wordAlternation(Set<String> words) {
        return "\\b(" + String.join("|", new TreeSet<>(words)) + ")\\b";
    }

    private static String operatorAlternation() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < OPERATORS.size(); i++) {
            if (i > 0) {
                sb.append('|');
            }
            sb.append(regexEscape(OPERATORS.get(i)));
        }
        return sb.toString();
    }

    private static String regexEscape(String s) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if ("\\^$.|?*+()[]{}".indexOf(c) >= 0) {
                sb.append('\\');
            }
            sb.append(c);
        }
        return sb.toString();
    }
}
