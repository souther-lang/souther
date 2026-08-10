package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source that departs from the canonical form departs at some rule's unit.
 *
 * <p>This is the check the whole issue rests on, and it is the one that cannot be written from the
 * rules: asked of the rules, a departure none of them holds is not a departure. So the candidates
 * are made from the text and put to the parser — one line of a canonical form written differently,
 * kept where the grammar still admits it and where the canonical form of what is written is the one
 * it came from. Each of those is a source differing from its canonical form in one way and in no
 * other, and what is held is that the report names it and repairing what the rules say writes the
 * canonical form back.
 *
 * <p>Not from the formatter's own output. A departure it never writes is still one an author can
 * write, and three of the rules here were missing because the corpus never showed them: a top-level
 * line indented, a comment at a column of its own, a blank line at a place a group settles.
 *
 * <p>One candidate per kind of line rather than one per line, and the kind is read from the layout:
 * what broke in front of the line, what breaks after it, what is written at the start of it and how
 * deep it stands. Written from the characters instead — the word the line opens with and its column
 * — it would put a boundary an obligation broke, one a group settled and one a comment stands at
 * under one name, which is this check's own mistake made one level up.
 *
 * <p>Over this corpus that comes to a few hundred candidates of a few thousand lines. Every line of
 * every source, written every way, was run against these rules and named: 3823 of 3823. It is not
 * run that way here because it takes three minutes, and what the reduction rests on is the sentence
 * above rather than that measurement.
 */
class EveryDepartureFromTheCanonicalFormIsSomeRulesTest {

    /** A canonical form with one line of it written differently. */
    record Departure(String kind, String shape, String text, String canonical) {

        @Override
        public String toString() {
            return kind + " — " + shape;
        }
    }

    /**
     * What the sweep answered, so that the rows and the check that they are all of them are one
     * sweep. The corpus does not change while the class runs, and a second sweep of it would be the
     * same few hundred candidates built from the same few thousand lines.
     */
    private static List<Departure> swept;

    static Stream<Departure> departures() {
        if (swept == null) {
            swept = sweep();
        }
        return swept.stream();
    }

    private static List<Departure> sweep() {
        List<Departure> out = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        // Shortest first, and one candidate per shape across the whole corpus. A shape is a shape
        // wherever it stands, and asking about it in the smallest source that has it is the same
        // question asked of less text.
        List<String> corpus = new ArrayList<>(WhatGoesBetweenTwoTokensOnALineTest.corpus());
        corpus.sort(java.util.Comparator.comparingInt(String::length));
        for (String source : corpus) {
            Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(source).root());
            String canonical = form.layout().text();
            List<String> lines = List.of(canonical.split("\n", -1));
            List<String> shapes = shapesOf(form, lines);
            Declarations standing = Declarations.of(lines);
            for (int i = 0; i < lines.size(); i++) {
                Map<String, String> locally = standing == null ? null : standing.written(i);
                for (Map.Entry<String, String> m : written(lines, i).entrySet()) {
                    String text = m.getValue();
                    String shape = shapes.get(i);
                    if (text == null || text.equals(canonical)
                            || seen.contains(m.getKey() + " of " + shape)) {
                        continue;   // this shape is already among them, written this way
                    }
                    if (locally != null
                            && !standing.admits(m.getKey(), locally.get(m.getKey()), i)) {
                        continue;   // the declaration this line is in already answers no
                    }
                    // The parse is what says the grammar still admits it, and the formatter takes
                    // what it produced rather than the text it came from — the same answer without
                    // the second parse of every candidate.
                    CstParser.Result parsed = CstParser.parse(text);
                    if (!parsed.errors().isEmpty()
                            || !Formatter.format(parsed.root()).equals(canonical)) {
                        continue;   // not a departure: another source, with a canonical form of
                                    // its own. The shape is left to be met again, so a line the
                                    // grammar refuses one way of writing does not take the shape
                                    // out of the sweep.
                    }
                    seen.add(m.getKey() + " of " + shape);
                    out.add(new Departure(m.getKey(), shape, text, canonical));
                }
            }
        }
        return out;
    }

    /**
     * A canonical form cut into the declarations it is made of, so that a line written differently
     * is answered by the declaration it is in rather than by the whole file.
     *
     * <p>A candidate differs from its source in one line, and the formatter answers a module by
     * answering each of its declarations: put back together, a declaration canonicalised on its own
     * with the header in front is what stands there in the whole. So a declaration whose canonical
     * form the change did not survive is a change the whole file will not survive either, and that
     * is a smaller question — for the longest source here, one twenty-first of the text.
     *
     * <p>It is used to refuse and never to admit. What is kept is still decided by the whole file,
     * so nothing here decides what a departure is; the only thing a mistake in it can do is drop a
     * candidate, which the number of rows says.
     */
    private record Declarations(String header, List<List<String>> pieces, List<String> canonical,
            List<Integer> opensAt) {

        /**
         * The declarations of {@code lines}: what opens at column zero under a blank line, and the
         * header everything before the first of them.
         */
        static Declarations of(List<String> lines) {
            List<Integer> opens = new ArrayList<>();
            for (int i = 0; i < lines.size(); i++) {
                String line = lines.get(i);
                boolean opensOne = !line.isBlank() && !line.startsWith(" ")
                        && !line.startsWith("module") && !line.startsWith("import");
                if (opensOne && (i == 0 || lines.get(i - 1).isBlank())) {
                    opens.add(i);
                }
            }
            if (opens.size() < 2) {
                return null;   // one declaration is the whole file, and there is nothing to save
            }
            String header = String.join("\n", lines.subList(0, opens.get(0)));
            List<List<String>> pieces = new ArrayList<>();
            List<String> canonical = new ArrayList<>();
            for (int d = 0; d < opens.size(); d++) {
                int to = d + 1 < opens.size() ? opens.get(d + 1) : lines.size();
                List<String> piece = lines.subList(opens.get(d), to);
                pieces.add(piece);
                String alone = header + "\n" + String.join("\n", piece);
                CstParser.Result parsed = CstParser.parse(alone);
                // A declaration that will not stand on its own, or that the formatter writes
                // differently when it does, is one this cannot answer for. Its own canonical form
                // is recorded as absent and every candidate in it goes to the whole file.
                canonical.add(parsed.errors().isEmpty()
                        && Formatter.format(parsed.root()).equals(alone) ? alone : null);
            }
            return new Declarations(header, pieces, canonical, opens);
        }

        /** Which declaration line {@code i} is in, or -1 where this cannot answer for it. */
        private int at(int i) {
            for (int d = 0; d < opensAt.size(); d++) {
                int from = opensAt.get(d);
                int to = d + 1 < opensAt.size() ? opensAt.get(d + 1) : Integer.MAX_VALUE;
                if (i >= from && i < to) {
                    // The first line of a declaration and the last are where a blank line written
                    // in and two lines run together reach the declaration next door, which is a
                    // question about the file rather than about either of them.
                    return canonical.get(d) == null ? -1 : d;
                }
            }
            return -1;   // the header
        }

        /**
         * Whether writing line {@code i} that way reaches the declaration after it.
         *
         * <p>Two of them do: a line run on into the next one, and a blank line written under it.
         * Written under the last line of a declaration, both are about what stands between two of
         * them, which is the file's question and not either declaration's. The rest write the line
         * where it stands.
         *
         * <p>What this buys is the refusal below being sound rather than any row: filtering those
         * two as well leaves this corpus with the same 481, since none of them is admitted here
         * anyway. It is the local question being a part of the whole one that the refusal rests on,
         * and for these two it is not.
         */
        private boolean reachesTheNextOne(String kind, int i, int d) {
            int to = d + 1 < opensAt.size() ? opensAt.get(d + 1) : Integer.MAX_VALUE;
            boolean last = i == to - 1;
            return last && ("run on into the next line".equals(kind)
                    || "with a blank line under it".equals(kind));
        }

        /** Line {@code i} written every way, inside its declaration alone. */
        Map<String, String> written(int i) {
            int d = at(i);
            if (d < 0) {
                return null;
            }
            List<String> piece = pieces.get(d);
            return EveryDepartureFromTheCanonicalFormIsSomeRulesTest
                    .written(piece, i - opensAt.get(d));
        }

        /** Whether {@code local} is still the declaration's canonical form, written that way. */
        boolean admits(String kind, String local, int i) {
            int d = at(i);
            if (d < 0 || local == null || reachesTheNextOne(kind, i, d)) {
                return true;   // nothing was asked, so nothing is refused
            }
            String alone = header + "\n" + local;
            CstParser.Result parsed = CstParser.parse(alone);
            return parsed.errors().isEmpty()
                    && Formatter.format(parsed.root()).equals(canonical.get(d));
        }
    }

    /**
     * What each line of a canonical form is, in the terms the rules answer in.
     *
     * <p>Read from the layout and not from the characters. Two lines that open with the same word
     * at the same column can stand at boundaries three different rules answer for — one an
     * obligation broke, one a group settled, one a comment stands at — and a sweep that took them
     * for the same thing would ask about the first and drop the other two. That is the mistake this
     * whole check is written to avoid, made one level up.
     *
     * <p>So a line is named by what breaks in front of it, what breaks after it, what is written at
     * the start of it and how deep it stands. What is left over — which identifier is on it, how
     * long it is — is what a rule's answer does not turn on.
     */
    private static List<String> shapesOf(Formatter.CanonicalForm form, List<String> lines) {
        String text = form.layout().text();
        Map<Integer, Newline> ends = new LinkedHashMap<>();
        Map<Integer, Integer> depth = new LinkedHashMap<>();
        for (Newline n : form.layout().breaks()) {
            int line = (int) text.substring(0, n.offset()).chars().filter(c -> c == '\n').count();
            ends.putIfAbsent(line, n);
            depth.putIfAbsent(line + 1, n.under().size());
        }
        Map<Integer, Place> opened = new LinkedHashMap<>();
        form.layout().extents().forEach((place, extent) -> {
            Place standing = opened.get(extent.start());
            if (standing == null
                    || form.layout().extents().get(standing).end() < extent.end()) {
                opened.put(extent.start(), place);
            }
        });
        List<String> out = new ArrayList<>();
        int at = 0;
        for (int i = 0; i < lines.size(); i++) {
            String line = lines.get(i);
            String content = line.strip();
            Place place = opened.get(at + line.length() - line.stripLeading().length());
            String opens = content.isEmpty() ? "nothing"
                    : content.startsWith("//") ? "a comment"
                    : place != null ? place.construct().name()
                    : "no place";
            out.add(cause(ends.get(i - 1)) + " / " + opens + " / " + cause(ends.get(i))
                    + " at depth " + depth.getOrDefault(i, 0)
                    + " and column " + (line.length() - line.stripLeading().length()));
            at += line.length() + 1;
        }
        return out;
    }

    /** What wrote a break: the obligation it discharges, or the group that settled it. */
    private static String cause(Newline n) {
        if (n == null) {
            return "the start of the file";
        }
        return switch (n.cause()) {
            case Newline.Cause.Forced f -> f.obligation().name();
            case Newline.Cause.Settled _ -> "a group's own break";
        };
    }

    /** One line of a canonical form, written the ways an author could have written it. */
    private static Map<String, String> written(List<String> lines, int i) {
        Map<String, String> out = new LinkedHashMap<>();
        String line = lines.get(i);
        out.put("one column further in", replacing(lines, i, " " + line));
        out.put("one column back",
                line.startsWith(" ") ? replacing(lines, i, line.substring(1)) : null);
        out.put("at no column at all",
                line.startsWith(" ") ? replacing(lines, i, line.strip()) : null);
        out.put("run on into the next line", i + 1 < lines.size() ? joining(lines, i) : null);
        out.put("with a blank line under it", inserting(lines, i + 1));
        out.put("with a space at the end of it", replacing(lines, i, line + " "));
        int space = line.indexOf(' ', line.length() - line.stripLeading().length());
        out.put("with a space doubled in it", space > 0 && space < line.length() - 1
                ? replacing(lines, i, line.substring(0, space) + " " + line.substring(space))
                : null);
        out.put("with a space taken out of it",
                space > 0 && space + 1 < line.length() && line.charAt(space + 1) != ' '
                        ? replacing(lines, i, line.substring(0, space) + line.substring(space + 1))
                        : null);
        return out;
    }

    private static String replacing(List<String> lines, int i, String with) {
        List<String> copy = new ArrayList<>(lines);
        copy.set(i, with);
        return String.join("\n", copy);
    }

    private static String inserting(List<String> lines, int i) {
        List<String> copy = new ArrayList<>(lines);
        copy.add(i, "");
        return String.join("\n", copy);
    }

    private static String joining(List<String> lines, int i) {
        List<String> copy = new ArrayList<>(lines);
        copy.set(i, copy.get(i) + " " + copy.get(i + 1).stripLeading());
        copy.remove(i + 1);
        return String.join("\n", copy);
    }

    @ParameterizedTest(name = "{0}")
    @MethodSource("departures")
    void aDepartureIsNamedByARule(Departure departure) {
        Deviations.Report report = Deviations.of(departure.text());

        assertTrue(!report.deviations().isEmpty(),
                "no rule names it:\n" + departure.text());
        assertTrue(report.whole(),
                "what is named is not all of it: " + report.deviations() + "\n"
                        + departure.text());
    }

    /**
     * Every way of writing a line differently reached the parser, and each of them was admitted
     * somewhere.
     *
     * <p>A row that produced no candidate at all is a check that ran on nothing and said it passed,
     * which is what a sweep over generated candidates fails at silently.
     */
    @Test
    void andEveryWayOfWritingALineDifferentlyIsAmongThem() {
        Set<String> kinds = new LinkedHashSet<>();
        departures().forEach(d -> kinds.add(d.kind()));

        assertEquals(written(List.of("    let f (a: Int): Int = a", "    let g = a"), 0).keySet(),
                kinds, "a way of writing a line that no candidate was built for");
    }
}
