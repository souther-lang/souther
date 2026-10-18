package souther.compiler;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * The rows a {@code --generate} block writes, each read apart from the others: the behavior it is
 * under, the name it is written with if any, the lines said over it, and the row as written.
 *
 * <p>One reading for every test that asks a block about its rows. What a row is for is written in
 * two places — as its name, where it was composed for one thing that has one, and as a
 * {@code // fills} line over it otherwise and for what it is handed besides — and which of the two
 * holds a given thing is the generator's naming rule. A test that reads the text itself states that
 * rule again in its own words, and goes on reading it the old way when the rule moves.
 *
 * <p>The name is read by the lexer, which is what reads it when the row is pasted: a row is
 * {@code | "name" : (...)} or {@code | (...)}, and a row this cannot tell to be either is a failure
 * rather than a row with no name.
 */
public final class RowsOfABlock {

    private static final String ROW = "    | ";
    private static final String FILLS = "// fills ";

    private RowsOfABlock() {}

    /**
     * One row.
     *
     * @param behavior the behavior whose {@code example} block it is in
     * @param name     what it is named, as the string it denotes, or none
     * @param over     the comment lines directly over it, in order and as written
     * @param written  the row, its continuations joined to it where the formatter wrapped it
     */
    public record Row(String behavior, Optional<String> name, List<String> over, String written) {

        public Row {
            over = List.copyOf(over);
        }

        /**
         * The row past its name, its whitespace closed up: what it holds and what it answers, which
         * is what two blocks offering the same rows under other names have alike.
         */
        public String values() {
            List<GreenToken> tokens = CstLexer.lex(written).tokens();
            StringBuilder out = new StringBuilder();
            boolean past = name.isEmpty();
            for (GreenToken token : tokens) {
                if (past) {
                    out.append(token.text());
                } else if (token.kind() == SyntaxKind.COLON) {
                    past = true;
                }
            }
            String held = out.toString().replaceAll("\\s+", " ").trim();
            return held.startsWith("| ") ? held.substring(2) : held;
        }

        /** What is said over the row as filled, one thing a line. */
        public List<String> fills() {
            return over.stream().filter(line -> line.startsWith(FILLS))
                    .map(line -> line.substring(FILLS.length())).toList();
        }

        /**
         * Whether the row is said to be for {@code thing}, as its name or over it.
         *
         * <p>Only for a claim that does not turn on which of the two it is — what the row holds,
         * or that something is offered a row at all. A claim about how a row is named asks
         * {@link #name} and {@link #fills} apart.
         *
         * <p>A name is a thing's words, and a line over a row says the words and, where the thing
         * has one, its place in parentheses after them; so {@code thing} is the words.
         */
        public boolean isFor(String thing) {
            return name.filter(thing::equals).isPresent() || fills().stream()
                    .anyMatch(said -> said.equals(thing) || said.startsWith(thing + " ("));
        }
    }

    /** Every row {@code block} writes, in its order. */
    public static List<Row> of(String block) {
        List<String> lines = block.lines().toList();
        List<Row> out = new ArrayList<>();
        String behavior = null;
        for (int at = 0; at < lines.size(); at++) {
            String line = lines.get(at);
            if (line.startsWith("example ")) {
                behavior = line.substring("example ".length()).trim();
            }
            if (!line.startsWith(ROW)) {
                continue;
            }
            if (behavior == null) {
                throw new AssertionError("a row is written under an example block: " + block);
            }
            int top = at;
            while (top > 0 && lines.get(top - 1).startsWith("//")) {
                top--;
            }
            List<String> over = lines.subList(top, at);
            StringBuilder written = new StringBuilder(line);
            while (at + 1 < lines.size() && continues(lines.get(at + 1))) {
                written.append('\n').append(lines.get(++at));
            }
            out.add(new Row(behavior, nameOf(written.toString()), over, written.toString()));
        }
        return out;
    }

    /** The one row {@code block} writes whose text holds {@code inputs}. */
    public static Row at(String block, String inputs) {
        List<Row> at = of(block).stream().filter(row -> row.written().contains(inputs)).toList();
        if (at.size() != 1) {
            throw new AssertionError("one row is written at " + inputs + ": " + block);
        }
        return at.getFirst();
    }

    /** The one row {@code block} says is for {@code thing}, as its name or over it. */
    public static Row forThe(String block, String thing) {
        List<Row> at = of(block).stream().filter(row -> row.isFor(thing)).toList();
        if (at.size() != 1) {
            throw new AssertionError("one row is offered for " + thing + ": " + block);
        }
        return at.getFirst();
    }

    /** A line the formatter wrapped a row onto: indented past the bar that starts the row. */
    private static boolean continues(String line) {
        return line.startsWith(ROW.replace("| ", "  ")) && !line.isBlank();
    }

    private static Optional<String> nameOf(String row) {
        List<GreenToken> tokens = CstLexer.lex(row).tokens().stream()
                .filter(token -> !token.kind().isTrivia() && token.kind() != SyntaxKind.EOF)
                .toList();
        if (tokens.size() >= 3 && tokens.get(0).kind() == SyntaxKind.PIPE) {
            if (tokens.get(1).kind() == SyntaxKind.STRING_LIT
                    && tokens.get(2).kind() == SyntaxKind.COLON) {
                return Optional.of(CstLexer.textOf(tokens.get(1).text()));
            }
            if (tokens.get(1).kind() == SyntaxKind.LPAREN) {
                return Optional.empty();
            }
        }
        throw new AssertionError("a row is written with a name or with none: " + row);
    }
}
