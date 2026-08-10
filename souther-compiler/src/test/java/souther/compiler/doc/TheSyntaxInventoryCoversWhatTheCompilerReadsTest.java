package souther.compiler.doc;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.SyntaxKind;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The inventory in {@code grammar} covers the closed sets the compiler holds.
 *
 * <p>A token, a delimiter and an operator are sets the lexer has, so a list of them written down
 * can be held to them. The specification had two such lists and nothing compared either: the
 * reserved words omitted {@code unreachable} and carried {@code on}, which its own next paragraph
 * says is not one, and the operators were missing every bracket, the colon and the comma.
 *
 * <p>The rest of the inventory is not checked here and cannot be. No set the compiler enumerates
 * says which {@code then} an {@code else} closes, or what a `data` declaration looks like; those
 * rows are the specification's own and are held by whatever states them.
 *
 * <p>The table is read by its declared role, and its separator is read from the same attribute, so
 * what this depends on is the contract the table announces and not the shape of the prose around
 * it.
 */
class TheSyntaxInventoryCoversWhatTheCompilerReadsTest {

    private static final String INDEX = "grammar";
    private static final String ROLE = "syntax-inventory";
    private static final String WHERE_THE_WORDS_ARE_LISTED = "reserved-words";

    /** The kinds of row whose contents the lexer can be asked about. */
    private static final Set<String> CHECKED = Set.of("token", "delimiter", "operator");

    /** A symbol as the document writes one: {@code `+==+`}, or {@code `{plus}`} where a literal
     *  {@code +} would end the passthrough it opened. */
    private static final Pattern WRITTEN = Pattern.compile("`([^`]+)`");

    /**
     * A token the lexer makes and no production reads, so it is not a form the language has and the
     * inventory does not list it. Removing it from the lexer is #569; when that lands this stops
     * being a token at all and the assertion below says so.
     */
    private static final String LEXED_BUT_UNREAD = "<-";

    @Test
    void everySymbolTheKindsSpellIsInTheInventory() {
        Set<String> spelled = new TreeSet<>(symbolsTheKindsSpell());
        assertTrue(spelled.remove(LEXED_BUT_UNREAD),
                "`" + LEXED_BUT_UNREAD + "` is no longer a kind at all, so the inventory no longer"
                        + " has to leave it out — drop this exception");
        assertEquals(spelled, new TreeSet<>(symbolsTheInventoryLists()),
                "the inventory and the kinds disagree about the symbols the language has");
    }

    @Test
    void theReservedWordsAreTheOnesTheLexerReserves() {
        assertEquals(new TreeSet<>(CstLexer.keywords()), new TreeSet<>(wordsTheDocumentLists()),
                "the reserved words the specification lists are not the ones the lexer reserves");
    }

    /**
     * Each punctuation and operator, as {@link SyntaxKind} spells it. The lexer is not run: what is
     * read is the kinds' own account of how each is written.
     *
     * <p>A symbol is a spelling with no letter in it, which is what separates one from a keyword and
     * from the kinds of the tree above the leaves — those spell themselves out of their own names,
     * and a name is letters. One enum holds both the leaves and the nodes, so that is the only
     * handle there is; a kind above the leaves that spelled itself with punctuation would be taken
     * for a symbol, and what would fix that is the enum saying which of its constants are tokens.
     */
    private static Set<String> symbolsTheKindsSpell() {
        Set<String> symbols = new LinkedHashSet<>();
        for (SyntaxKind kind : SyntaxKind.values()) {
            if (kind.display() instanceof String spelled) {
                String written = spelled.replace("`", "");
                if (written.chars().noneMatch(Character::isLetter)) {
                    symbols.add(written);
                }
            }
        }
        return symbols;
    }

    /** Each symbol the inventory writes in a row the lexer can be asked about. */
    private static Set<String> symbolsTheInventoryLists() {
        Set<String> listed = new LinkedHashSet<>();
        for (List<String> row : inventory()) {
            if (!CHECKED.contains(row.get(1))) {
                continue;
            }
            Matcher written = WRITTEN.matcher(row.getFirst());
            while (written.find()) {
                String spelled = plain(written.group(1));
                if (spelled != null) {
                    listed.add(spelled);
                }
            }
        }
        return listed;
    }

    /** What the document meant by one written span, or null where the span is not a symbol. */
    private static String plain(String written) {
        String plus = written.replace("{plus}", "+");
        if (plus.equals(written) && written.length() > 2
                && written.startsWith("+") && written.endsWith("+")) {
            return written.substring(1, written.length() - 1);
        }
        return plus.equals(written) ? null : plus;
    }

    /** The inventory's rows, header dropped, each as its cells. */
    private static List<List<String>> inventory() {
        List<String> lines = SpecDocument.bundled().section(INDEX).body().lines().toList();
        int declared = -1;
        for (int i = 0; i < lines.size(); i++) {
            if (lines.get(i).contains("role=\"" + ROLE + "\"")) {
                declared = i;
                break;
            }
        }
        assertTrue(declared >= 0, "`" + INDEX + "` declares no `" + ROLE + "` table");
        Matcher separator = Pattern.compile("separator=(\\S)").matcher(lines.get(declared));
        assertTrue(separator.find(), "the table does not say what separates its cells");
        String cell = separator.group(1);
        String edge = cell + "===";

        List<List<String>> rows = new java.util.ArrayList<>();
        for (String line : lines.subList(declared + 2, lines.size())) {
            if (line.equals(edge)) {
                break;
            }
            if (line.isBlank()) {
                continue;
            }
            List<String> cells = java.util.Arrays.stream(line.split(Pattern.quote(cell)))
                    .skip(1).map(String::strip).toList();
            assertEquals(3, cells.size(), "a row is a form, a kind and where it is given: " + line);
            rows.add(cells);
        }
        assertTrue(rows.size() > 1, "the inventory has no rows");
        return rows.subList(1, rows.size());
    }

    /** The words the specification's own block lists, whitespace being all that separates them. */
    private static List<String> wordsTheDocumentLists() {
        List<String> lines = SpecDocument.bundled().section(WHERE_THE_WORDS_ARE_LISTED)
                .body().lines().toList();
        int opened = lines.indexOf("----");
        assertTrue(opened >= 0, "the reserved words are not written as a block");
        List<String> words = new java.util.ArrayList<>();
        for (String line : lines.subList(opened + 1, lines.size())) {
            if (line.equals("----")) {
                break;
            }
            words.addAll(java.util.Arrays.stream(line.strip().split("\\s+")).toList());
        }
        return words;
    }
}
