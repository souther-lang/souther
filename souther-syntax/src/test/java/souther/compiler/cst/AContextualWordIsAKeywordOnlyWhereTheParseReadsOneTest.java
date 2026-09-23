package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where the parse reads a {@link ContextualWord} as a keyword, the tree says so, and where the same
 * spelling is a name, the tree says that.
 *
 * <p>Every reader downstream — the builder, the formatter, the editor's highlighting — asks the
 * tree which of the two a word was and does not work it out again. So what is held here is the
 * whole of what they rely on: a word the parse took for a keyword is a {@link
 * SyntaxKind#CONTEXTUAL_KW}, and the same spelling written as a name is an {@link SyntaxKind#IDENT}.
 *
 * <p>The sources are written out rather than generated from the vocabulary, one of each per word,
 * and a word added with none here fails for want of them. Generating them would ask the vocabulary
 * whether the vocabulary agrees with itself.
 */
class AContextualWordIsAKeywordOnlyWhereTheParseReadsOneTest {

    /** A source in which the word is read as a keyword. */
    private static final Map<ContextualWord, String> READ_AS_A_KEYWORD = readAsAKeyword();

    /** A source in which the same spelling is a name. */
    private static final Map<ContextualWord, String> WRITTEN_AS_A_NAME = writtenAsAName();

    private static Map<ContextualWord, String> readAsAKeyword() {
        Map<ContextualWord, String> sources = new LinkedHashMap<>();
        sources.put(ContextualWord.EXAMPLES, "examples for m\n");
        sources.put(ContextualWord.FOR, "examples for m\n");
        sources.put(ContextualWord.EXAMPLE, "example f\n    | (1) -> 1\n");
        sources.put(ContextualWord.FAKE, "fake f\n    | _ -> 1\n");
        sources.put(ContextualWord.PRIVATE, "private let f (x) = x\n");
        sources.put(ContextualWord.PARTIAL, "partial let f (x) = x\n");
        sources.put(ContextualWord.ON, "behavior f : (x: Int) -> Int\n    depends on g\n");
        sources.put(ContextualWord.INTRINSIC, "let f (x: Int): Int = intrinsic \"int.f\"\n");
        return sources;
    }

    private static Map<ContextualWord, String> writtenAsAName() {
        Map<ContextualWord, String> sources = new LinkedHashMap<>();
        sources.put(ContextualWord.EXAMPLES, "let f (examples) = examples\n");
        sources.put(ContextualWord.FOR, "let f (for) = for\n");
        sources.put(ContextualWord.EXAMPLE, "import example.m ( a )\n");
        sources.put(ContextualWord.FAKE, "let fake = 1\n");
        sources.put(ContextualWord.PRIVATE, "let f (private) = private\n");
        sources.put(ContextualWord.PARTIAL, "let f (partial) = partial\n");
        sources.put(ContextualWord.ON, "data A = { on: Int }\n");
        sources.put(ContextualWord.INTRINSIC, "let f (intrinsic) = intrinsic\n");
        return sources;
    }

    @Test
    void everyWordHasASourceOfEachHere() {
        List<ContextualWord> unwitnessed = new ArrayList<>();
        for (ContextualWord word : ContextualWord.values()) {
            if (!READ_AS_A_KEYWORD.containsKey(word) || !WRITTEN_AS_A_NAME.containsKey(word)) {
                unwitnessed.add(word);
            }
        }
        assertEquals(List.of(), unwitnessed, "a word nothing here is written for");
    }

    @Test
    void whereTheParseReadsAKeywordTheTreeHoldsOne() {
        List<String> wrong = new ArrayList<>();
        READ_AS_A_KEYWORD.forEach((word, source) -> {
            SyntaxNode root = parsedCleanly(source, wrong);
            if (!spelledAs(root, SyntaxKind.CONTEXTUAL_KW).contains(word.spelling())) {
                wrong.add(word + " is not a keyword in: " + source.strip());
            }
            if (spelledAs(root, SyntaxKind.IDENT).contains(word.spelling())) {
                wrong.add(word + " is left a name in: " + source.strip());
            }
        });
        assertEquals(List.of(), wrong);
    }

    @Test
    void whereTheSpellingIsANameTheTreeHoldsAName() {
        List<String> wrong = new ArrayList<>();
        WRITTEN_AS_A_NAME.forEach((word, source) -> {
            SyntaxNode root = parsedCleanly(source, wrong);
            if (!spelledAs(root, SyntaxKind.CONTEXTUAL_KW).isEmpty()) {
                wrong.add("a keyword was read in: " + source.strip());
            }
            if (!spelledAs(root, SyntaxKind.IDENT).contains(word.spelling())) {
                wrong.add(word + " is not a name in: " + source.strip());
            }
        });
        assertEquals(List.of(), wrong);
    }

    /** A source that does not parse would witness recovery, not the word. */
    private static SyntaxNode parsedCleanly(String source, List<String> wrong) {
        CstParser.Result parsed = CstParser.parse(source);
        if (!parsed.errors().isEmpty()) {
            wrong.add("does not parse: " + source.strip() + " " + parsed.errors());
        }
        return parsed.root();
    }

    private static List<String> spelledAs(SyntaxNode node, SyntaxKind kind) {
        List<String> out = new ArrayList<>();
        collect(node, kind, out);
        return out;
    }

    private static void collect(SyntaxNode node, SyntaxKind kind, List<String> out) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                collect(child, kind, out);
            } else if (e.kind() == kind) {
                out.add(((SyntaxToken) e).text());
            }
        }
    }
}
