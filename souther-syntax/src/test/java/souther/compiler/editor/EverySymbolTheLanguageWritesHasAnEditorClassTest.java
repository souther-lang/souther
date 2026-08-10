package souther.compiler.editor;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.SyntaxKind;
import org.junit.jupiter.api.Test;

import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The classification answers for exactly the symbols the language writes.
 *
 * <p>Held in both directions. A symbol left out is the failure this is here for: an editor's
 * classification is written by hand, and a symbol added to the language would otherwise be neither
 * painted nor deliberately unpainted, and would arrive in an editor as whatever the default was.
 * A kind classified that is not a symbol is the other side of it, and a covering alone would pass
 * with a name or a literal listed as an operator.
 *
 * <p>What this does not say is which side a symbol belongs on. That is a judgement about reading
 * rather than something the kinds decide, and it is written out in {@link EditorSymbols}.
 */
class EverySymbolTheLanguageWritesHasAnEditorClassTest {

    @Test
    void theClassifiedKindsAreTheSymbolsTheKindsSpell() {
        Set<SyntaxKind> classified = new TreeSet<>(EditorSymbols.operators());
        classified.addAll(EditorSymbols.punctuation());

        assertEquals(symbolKinds(), classified,
                "the editor's classification and the kinds disagree about which symbols the "
                        + "language writes");
    }

    @Test
    void noKindIsBothPaintedAndNot() {
        Set<SyntaxKind> both = new TreeSet<>(EditorSymbols.operators());
        both.retainAll(EditorSymbols.punctuation());

        assertEquals(Set.of(), both, "a symbol is painted as an operator or left alone, not both");
    }

    /** Every symbol the language writes: the kinds that spell themselves, less the reserved words,
     *  which are coloured as words. */
    private static Set<SyntaxKind> symbolKinds() {
        Set<String> words = CstLexer.keywords();
        Set<SyntaxKind> symbols = new TreeSet<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            kind.fixedSpelling().filter(spelled -> !words.contains(spelled))
                    .ifPresent(spelled -> symbols.add(kind));
        }
        return symbols;
    }
}
