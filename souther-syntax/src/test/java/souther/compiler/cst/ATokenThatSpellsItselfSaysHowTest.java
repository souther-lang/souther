package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link SyntaxKind#lexis()} and {@link SyntaxKind#fixedSpelling()} say the same thing about a kind
 * from two sides, and here they are held to each other.
 *
 * <p>The first is total — it has no default arm, so a constant added to the enum does not compile
 * until it is placed. The second is not, and cannot be: a spelling is a value, and a switch that
 * returns one falls back rather than refusing. That asymmetry is the whole reason this test exists.
 * Without it, a symbol added to the enum and placed among the tokens that spell themselves would
 * silently have no spelling, and every reader that asks the kinds which symbols the language has —
 * the specification's inventory, the editor grammar — would be answered a set one short.
 *
 * <p>The lists are deliberately not derived from one another. Deriving either would make the
 * agreement hold by construction, which is a check that cannot fail.
 */
class ATokenThatSpellsItselfSaysHowTest {

    @Test
    void everyTokenThatSpellsItselfHasASpelling() {
        List<SyntaxKind> unspelled = new ArrayList<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            if (kind.lexis() == SyntaxKind.Lexis.FIXED_TOKEN && kind.fixedSpelling().isEmpty()) {
                unspelled.add(kind);
            }
        }
        assertEquals(List.of(), unspelled,
                "these kinds are held to spell themselves and do not say how");
    }

    @Test
    void nothingElseSpellsItself() {
        List<SyntaxKind> spelled = new ArrayList<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            if (kind.lexis() != SyntaxKind.Lexis.FIXED_TOKEN && kind.fixedSpelling().isPresent()) {
                spelled.add(kind);
            }
        }
        assertEquals(List.of(), spelled,
                "a node and a token the source spells have no spelling of their own to give");
    }

    /**
     * A spelling names one kind. Two kinds claiming the same text would leave the readers of this
     * set — which ask what the language writes, not which kind writes it — with a form whose
     * meaning depends on which of the two answered.
     */
    @Test
    void noSpellingIsClaimedTwice() {
        Map<String, List<SyntaxKind>> byText = new LinkedHashMap<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            kind.fixedSpelling().ifPresent(
                    text -> byText.computeIfAbsent(text, t -> new ArrayList<>()).add(kind));
        }
        Map<String, List<SyntaxKind>> shared = new LinkedHashMap<>();
        byText.forEach((text, kinds) -> {
            if (kinds.size() > 1) {
                shared.put(text, kinds);
            }
        });
        assertEquals(Map.of(), shared, "one spelling, one kind");
    }

    /**
     * The spelling is what the lexer makes of it.
     *
     * <p>A kind saying how it is written is only worth reading if the lexer agrees, and nothing but
     * this holds the two together — the enum does not lex and the lexer does not consult the enum.
     * A spelling that no longer reaches its own kind is a lexical rule that moved out from under a
     * form the rest of the compiler still publishes.
     */
    @Test
    void lexingASpellingGivesBackItsOwnKind() {
        List<String> wrong = new ArrayList<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            Optional<String> spelling = kind.fixedSpelling();
            if (spelling.isEmpty()) {
                continue;
            }
            List<GreenToken> lexed = CstLexer.lex(spelling.get()).tokens().stream()
                    .filter(token -> !token.kind().isTrivia() && token.kind() != SyntaxKind.EOF)
                    .toList();
            if (lexed.size() != 1 || lexed.getFirst().kind() != kind) {
                wrong.add(kind + " spells `" + spelling.get() + "`, which lexes as "
                        + lexed.stream().map(GreenToken::kind).toList());
            }
        }
        assertEquals(List.of(), wrong, "a spelling does not reach the kind that claims it");
    }
}
