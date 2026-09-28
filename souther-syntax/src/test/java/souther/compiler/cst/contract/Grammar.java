package souther.compiler.cst.contract;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * {@code syntax/grammar.ebnf}, read into its productions.
 *
 * <p>The grammar is the contract and is not executed here: nothing parses Souther with it. What is
 * read is its structure — which productions there are, which are nodes of the contract tree, what
 * each refers to, which terminals it writes, and which tagged region each lies in — so that a
 * grammar the notation at its head does not describe is refused rather than published, and so that
 * the vocabulary and the corpus can be held to what it says.
 */
record Grammar(List<Production> productions, List<Region> regions) {

    Grammar {
        productions = List.copyOf(productions);
        regions = List.copyOf(regions);
    }

    /** One production: {@code [@node] name[Params] = body ;}, and the line it begins on. */
    record Production(String name, boolean node, List<String> parameters, Expr body, int line) {
        Production {
            parameters = List.copyOf(parameters);
        }
    }

    /** A tagged region, {@code tag::name[]} to {@code end::name[]}, and the productions inside it. */
    record Region(String tag, List<String> productions) {
        Region {
            productions = List.copyOf(productions);
        }
    }

    /** What a production's body is made of. */
    sealed interface Expr permits Reference, Terminal, Special, Sequence, Choice, Optional,
            Repetition, Except, If, NotAhead, Condition {
    }

    /** A reference to a production, with the parameters it turns on or off. */
    record Reference(String name, Map<String, Boolean> arguments) implements Expr {
        Reference {
            arguments = Map.copyOf(arguments);
        }
    }

    record Terminal(String text) implements Expr {
    }

    /** {@code ? text ?}: a set of characters stated in words. */
    record Special(String text) implements Expr {
    }

    record Sequence(List<Expr> parts) implements Expr {
        Sequence {
            parts = List.copyOf(parts);
        }
    }

    record Choice(List<Expr> alternatives) implements Expr {
        Choice {
            alternatives = List.copyOf(alternatives);
        }
    }

    record Optional(Expr body) implements Expr {
    }

    record Repetition(Expr body) implements Expr {
    }

    record Except(Expr from, Expr excepted) implements Expr {
    }

    /** {@code <if Parameter>}. */
    record If(String parameter) implements Expr {
    }

    /** {@code <not-ahead X>}. */
    record NotAhead(Expr ahead) implements Expr {
    }

    /** A restriction the notation defines in words: {@code <no-line-break>} and the like. */
    record Condition(String name) implements Expr {
    }

    /** The restrictions the notation defines by name alone. */
    static final Set<String> CONDITIONS = Set.of("no-line-break", "arm-column", "pipe-owner");

    Production production(String name) {
        for (Production each : productions) {
            if (each.name().equals(name)) {
                return each;
            }
        }
        throw new IllegalArgumentException("the grammar has no production " + name);
    }

    /** The names of the productions marked {@code @node}: the identifiers the contract tree uses. */
    Set<String> nodes() {
        Set<String> out = new LinkedHashSet<>();
        for (Production each : productions) {
            if (each.node()) {
                out.add(each.name());
            }
        }
        return out;
    }

    Region region(String tag) {
        for (Region each : regions) {
            if (each.tag().equals(tag)) {
                return each;
            }
        }
        throw new IllegalArgumentException("the grammar has no region " + tag);
    }

    /**
     * The productions of the lexical grammar. The grammar's head names the region tagged
     * {@code lexical} as the boundary: what is inside says how characters make tokens, and every
     * production after it is the structural grammar, which says how tokens make the tree.
     */
    Set<String> lexical() {
        return new LinkedHashSet<>(region("lexical").productions());
    }

    /** Every terminal the structural grammar writes: each one a token, not a character. */
    Set<String> structuralTerminals() {
        Set<String> out = new LinkedHashSet<>();
        for (Production each : structural()) {
            for (Expr part : everyPart(each.body())) {
                if (part instanceof Terminal it) {
                    out.add(it.text());
                }
            }
        }
        return out;
    }

    /** The lexical productions the structural grammar names, which are the tokens it reads. */
    Set<String> lexicalNamedByTheStructure() {
        Set<String> lexical = lexical();
        Set<String> out = new LinkedHashSet<>();
        for (Production each : structural()) {
            for (Reference reference : references(each.body())) {
                if (lexical.contains(reference.name())) {
                    out.add(reference.name());
                }
            }
        }
        return out;
    }

    private List<Production> structural() {
        Set<String> lexical = lexical();
        return productions.stream().filter(each -> !lexical.contains(each.name())).toList();
    }

    /** Every {@code ? text ?} the productions write, in the order they write them. */
    List<Special> specials() {
        List<Special> out = new ArrayList<>();
        for (Production each : productions) {
            for (Expr part : everyPart(each.body())) {
                if (part instanceof Special it) {
                    out.add(it);
                }
            }
        }
        return out;
    }

    /** Every reference {@code expr} makes, in the order it makes them. */
    static List<Reference> references(Expr expr) {
        List<Reference> out = new ArrayList<>();
        for (Expr part : everyPart(expr)) {
            if (part instanceof Reference it) {
                out.add(it);
            }
        }
        return out;
    }

    /** Every {@code <if P>} {@code expr} writes. */
    static List<If> conditionsOnParameters(Expr expr) {
        List<If> out = new ArrayList<>();
        for (Expr part : everyPart(expr)) {
            if (part instanceof If it) {
                out.add(it);
            }
        }
        return out;
    }

    /**
     * {@code expr} and every expression inside it, outermost first. The one walk every question
     * above is asked of, so a kind of expression added to the notation is walked into by all of
     * them or by none.
     */
    static List<Expr> everyPart(Expr expr) {
        List<Expr> out = new ArrayList<>();
        collectParts(expr, out);
        return out;
    }

    private static void collectParts(Expr expr, List<Expr> into) {
        into.add(expr);
        switch (expr) {
            case Sequence it -> it.parts().forEach(part -> collectParts(part, into));
            case Choice it -> it.alternatives().forEach(part -> collectParts(part, into));
            case Optional it -> collectParts(it.body(), into);
            case Repetition it -> collectParts(it.body(), into);
            case Except it -> {
                collectParts(it.from(), into);
                collectParts(it.excepted(), into);
            }
            case NotAhead it -> collectParts(it.ahead(), into);
            case Reference _, Terminal _, Special _, If _, Condition _ -> {
            }
        }
    }

    // --- reading -------------------------------------------------------------------------------

    private static final Pattern MARKER = Pattern.compile("(tag|end)::([a-z0-9-]+)\\[]");

    /** The grammar {@code text} writes. Refuses a text the notation does not describe. */
    static Grammar read(String text) {
        return new Reader(text).grammar();
    }

    private static final class Reader {
        private final String text;
        private int pos;
        private int line = 1;
        private final List<Production> productions = new ArrayList<>();
        private final Map<String, List<String>> regions = new LinkedHashMap<>();
        private final List<String> open = new ArrayList<>();

        Reader(String text) {
            this.text = text;
        }

        Grammar grammar() {
            skipSpaceAndComments();
            while (pos < text.length()) {
                Production production = production();
                productions.add(production);
                for (String tag : open) {
                    regions.get(tag).add(production.name());
                }
                skipSpaceAndComments();
            }
            if (!open.isEmpty()) {
                throw failure("a region is never closed: " + open);
            }
            List<Region> read = new ArrayList<>();
            regions.forEach((tag, names) -> read.add(new Region(tag, names)));
            return new Grammar(productions, read);
        }

        private Production production() {
            int begins = line;
            boolean node = false;
            if (text.startsWith("@node", pos)) {
                node = true;
                pos += "@node".length();
                skipSpaceAndComments();
            }
            String name = name();
            List<String> parameters = new ArrayList<>();
            if (pos < text.length() && text.charAt(pos) == '[') {
                pos++;
                do {
                    skipSpaceAndComments();
                    parameters.add(word());
                    skipSpaceAndComments();
                } while (take(','));
                expect(']');
            }
            skipSpaceAndComments();
            expect('=');
            Expr body = choice();
            skipSpaceAndComments();
            expect(';');
            return new Production(name, node, parameters, body, begins);
        }

        private Expr choice() {
            List<Expr> alternatives = new ArrayList<>();
            alternatives.add(sequence());
            skipSpaceAndComments();
            while (take('|')) {
                alternatives.add(sequence());
                skipSpaceAndComments();
            }
            return alternatives.size() == 1 ? alternatives.getFirst() : new Choice(alternatives);
        }

        private Expr sequence() {
            List<Expr> parts = new ArrayList<>();
            parts.add(except());
            skipSpaceAndComments();
            while (take(',')) {
                parts.add(except());
                skipSpaceAndComments();
            }
            return parts.size() == 1 ? parts.getFirst() : new Sequence(parts);
        }

        private Expr except() {
            Expr from = primary();
            skipSpaceAndComments();
            if (take('-')) {
                return new Except(from, primary());
            }
            return from;
        }

        private Expr primary() {
            skipSpaceAndComments();
            if (pos >= text.length()) {
                throw failure("the text ends inside a production");
            }
            char c = text.charAt(pos);
            return switch (c) {
                case '"', '\'' -> new Terminal(quoted(c));
                case '?' -> new Special(quoted('?').strip());
                case '[' -> new Optional(enclosed(']'));
                case '{' -> new Repetition(enclosed('}'));
                case '(' -> enclosed(')');
                case '<' -> restriction();
                default -> reference();
            };
        }

        /** What a bracket at the cursor encloses, up to the {@code closing} one. */
        private Expr enclosed(char closing) {
            pos++;
            Expr body = choice();
            expect(closing);
            return body;
        }

        private Expr restriction() {
            expect('<');
            String name = name();
            skipSpaceAndComments();
            Expr read;
            if (name.equals("if")) {
                read = new If(word());
                skipSpaceAndComments();
            } else if (name.equals("not-ahead")) {
                read = new NotAhead(choice());
            } else if (CONDITIONS.contains(name)) {
                read = new Condition(name);
            } else {
                throw failure("a restriction the notation does not define: <" + name + ">");
            }
            expect('>');
            return read;
        }

        private Expr reference() {
            String name = name();
            Map<String, Boolean> arguments = new LinkedHashMap<>();
            if (pos < text.length() && text.charAt(pos) == '[') {
                pos++;
                do {
                    skipSpaceAndComments();
                    boolean on;
                    if (take('+')) {
                        on = true;
                    } else if (take('~')) {
                        on = false;
                    } else {
                        throw failure("an argument is written `+P` or `~P`");
                    }
                    String parameter = word();
                    if (arguments.put(parameter, on) != null) {
                        throw failure("a parameter given twice: " + parameter);
                    }
                    skipSpaceAndComments();
                } while (take(','));
                expect(']');
            }
            return new Reference(name, arguments);
        }

        /** A production's name: lower-case words joined by {@code -}. */
        private String name() {
            int start = pos;
            if (pos >= text.length() || text.charAt(pos) < 'a' || text.charAt(pos) > 'z') {
                throw failure("a name was expected");
            }
            while (pos < text.length()) {
                if (isNameCharacter(text.charAt(pos))) {
                    pos++;
                } else if (text.charAt(pos) == '-' && pos + 1 < text.length()
                        && isNameCharacter(text.charAt(pos + 1))) {
                    pos += 2;
                } else {
                    break;
                }
            }
            return text.substring(start, pos);
        }

        private static boolean isNameCharacter(char c) {
            return (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9');
        }

        /** A parameter's name: a capitalised word. */
        private String word() {
            int start = pos;
            while (pos < text.length() && Character.isLetter(text.charAt(pos))) {
                pos++;
            }
            if (pos == start || !Character.isUpperCase(text.charAt(start))) {
                throw failure("a parameter's name was expected");
            }
            return text.substring(start, pos);
        }

        private String quoted(char quote) {
            expect(quote);
            int start = pos;
            int end = text.indexOf(quote, pos);
            if (end < 0) {
                throw failure("a " + quote + " is never closed");
            }
            String inside = text.substring(start, end);
            line += (int) inside.chars().filter(c -> c == '\n').count();
            pos = end + 1;
            if (inside.isEmpty()) {
                throw failure("an empty terminal");
            }
            return inside;
        }

        private void skipSpaceAndComments() {
            while (pos < text.length()) {
                char c = text.charAt(pos);
                if (c == '\n') {
                    line++;
                    pos++;
                } else if (Character.isWhitespace(c)) {
                    pos++;
                } else if (text.startsWith("(*", pos)) {
                    int end = text.indexOf("*)", pos + 2);
                    if (end < 0) {
                        throw failure("a comment is never closed");
                    }
                    comment(text.substring(pos + 2, end));
                    pos = end + 2;
                } else {
                    return;
                }
            }
        }

        /** Reads a comment for the region markers it holds, and counts its lines. */
        private void comment(String body) {
            Matcher marker = MARKER.matcher(body);
            while (marker.find()) {
                String tag = marker.group(2);
                if (marker.group(1).equals("tag")) {
                    if (regions.containsKey(tag)) {
                        throw failure("a region opened twice: " + tag);
                    }
                    regions.put(tag, new ArrayList<>());
                    open.add(tag);
                } else if (!open.remove(tag)) {
                    throw failure("a region closed that is not open: " + tag);
                }
            }
            line += (int) body.chars().filter(c -> c == '\n').count();
        }

        private boolean take(char c) {
            skipSpaceAndComments();
            if (pos < text.length() && text.charAt(pos) == c) {
                pos++;
                return true;
            }
            return false;
        }

        private void expect(char c) {
            if (!take(c)) {
                throw failure("expected `" + c + "`");
            }
        }

        private IllegalArgumentException failure(String what) {
            return new IllegalArgumentException("grammar.ebnf line " + line + ": " + what);
        }
    }
}
