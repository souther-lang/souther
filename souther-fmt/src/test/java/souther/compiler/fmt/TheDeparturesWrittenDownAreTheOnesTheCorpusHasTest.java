package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.test.ClosedWorldContract;
import souther.test.Nightly;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The departures written down beside {@link EveryDepartureFromTheCanonicalFormIsSomeRulesTest} are
 * the ones the corpus has: one line of a canonical form written differently, for every way of
 * writing it and every shape of line the corpus holds.
 *
 * <p>Where they come from. The candidates are made from the text and put to the parser — one line
 * of a canonical form written differently, kept where the grammar still admits it and where the
 * canonical form of what is written is the one it came from. Each of those is a source differing
 * from its canonical form in one way and in no other.
 *
 * <p>Not from the formatter's own output. A departure it never writes is still one an author can
 * write, and three of the rules there were missing because the corpus never showed them: a
 * top-level line indented, a comment at a column of its own, a blank line at a place a group
 * settles.
 *
 * <p>One candidate per kind of line rather than one per line, and the kind is read from the
 * layout: what broke in front of the line, what breaks after it, what is written at the start of
 * it and how deep it stands. Written from the characters instead — the word the line opens with and
 * its column — it would put a boundary an obligation broke, one a group settled and one a comment
 * stands at under one name, which is this sweep's own mistake made one level up.
 *
 * <p>What admits a candidate is the whole file it was found in, and what it is then written down as
 * is the declaration that line stands in, where that declaration can answer for it. Both are a
 * canonical form with one line of it written differently, and the smaller one is a tenth of the
 * text.
 *
 * <p><b>Once a night.</b> Finding them is most of what the corpus costs to ask, and what is asked
 * of each of them — that a rule names it — is asked of the ones written down on every change. No
 * cheaper way to find them was found: the shapes are the corpus's, and the corpus is what has to be
 * read to know them. And what this finds is as well found by the morning as by the change that
 * caused it: a shape a source brings is a shape the rules are then asked about, and a rule that
 * stops naming a departure already written down is found on the change that stopped it. Rerun with
 * {@code -Dsouther.departures.update=true} to write down what the corpus has now.
 */
@ClosedWorldContract
@Nightly
class TheDeparturesWrittenDownAreTheOnesTheCorpusHasTest {

    private static final String UPDATE = "souther.departures.update";

    private static final Path SOURCE = Path.of("src/test/resources/souther/compiler/fmt",
            EveryDepartureFromTheCanonicalFormIsSomeRulesTest.RECORDED);

    @Test
    void theDeparturesWrittenDownAreTheOnesTheCorpusHas() throws IOException {
        List<EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written> found = sweep();
        found.sort(Comparator.comparing(
                EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written::pair));
        String now = EveryDepartureFromTheCanonicalFormIsSomeRulesTest.writtenDown(found);
        if (Boolean.getBoolean(UPDATE)) {
            Files.createDirectories(SOURCE.getParent());
            Files.writeString(SOURCE, now, StandardCharsets.UTF_8);
        }
        List<EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written> written =
                EveryDepartureFromTheCanonicalFormIsSomeRulesTest.recorded();

        List<String> gone = new ArrayList<>(pairs(written));
        gone.removeAll(pairs(found));
        List<String> arrived = new ArrayList<>(pairs(found));
        arrived.removeAll(pairs(written));
        assertEquals(pairs(written), pairs(found),
                "no longer found (" + gone.size() + "): " + head(gone)
                        + "\nnewly found (" + arrived.size() + "): " + head(arrived)
                        + "\nrerun with -D" + UPDATE + "=true once the change is the one intended");
        assertEquals(written, found, "the same shapes, written down as other sources; rerun with -D"
                + UPDATE + "=true once the change is the one intended");
    }

    private static List<String> pairs(List<EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written> of) {
        return of.stream().map(EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written::pair)
                .toList();
    }

    /** The first few of them, which is as much as a failure can usefully say. */
    private static String head(List<String> some) {
        return some.isEmpty() ? "none"
                : String.join("\n  ", some.subList(0, Math.min(5, some.size())))
                        + (some.size() > 5 ? "\n  … and " + (some.size() - 5) + " more" : "");
    }

    private static List<EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written> sweep() {
        List<EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written> out = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        // Shortest first, and one candidate per shape across the whole corpus. A shape is a shape
        // wherever it stands, and asking about it in the smallest source that has it is the same
        // question asked of less text.
        List<String> corpus = new ArrayList<>(WhatGoesBetweenTwoTokensOnALineTest.corpus());
        corpus.sort(Comparator.comparingInt(String::length));
        for (String source : corpus) {
            Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(source).root());
            String canonical = form.layout().text();
            List<String> lines = List.of(canonical.split("\n", -1));
            List<String> shapes = shapesOf(form, lines);
            Declarations standing = Declarations.of(lines);
            for (int i = 0; i < lines.size(); i++) {
                Map<String, String> locally = standing == null ? null : standing.written(i);
                for (Map.Entry<String, String> m
                        : EveryDepartureFromTheCanonicalFormIsSomeRulesTest.written(lines, i)
                                .entrySet()) {
                    String text = m.getValue();
                    String shape = shapes.get(i);
                    if (text == null || text.equals(canonical)
                            || seen.contains(m.getKey() + " of " + shape)) {
                        continue;   // this shape is already among them, written this way
                    }
                    Locally says = locally == null ? new Locally.NotAsked()
                            : standing.says(m.getKey(), locally.get(m.getKey()), i);
                    if (says instanceof Locally.Refused) {
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
                    // What is written down is the smallest text the departure was answered for.
                    // Where the declaration answered, that is the declaration; where it did not,
                    // the whole file is what was asked and is what is written down.
                    String asked = says instanceof Locally.Answered a ? a.text() : text;
                    out.add(new EveryDepartureFromTheCanonicalFormIsSomeRulesTest.Written(
                            m.getKey(), shape, asked));
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
     * <p>What is kept is still decided by the whole file, so nothing here decides what a departure
     * is; the only thing a mistake in it can do is drop a candidate, which the record written down
     * says. What it decides is how much text the departure is written down as: a declaration that
     * answered is one whose canonical form was checked here, so it is a source in its own right and
     * every property is asked of it as of any other.
     */
    private record Declarations(String header, List<List<String>> pieces, List<String> canonical,
            List<Integer> opensAt) {

        /**
         * The declarations of {@code lines}: what opens at column zero under a blank line, and the
         * header everything before the first of them.
         *
         * <p>The first declaration is the header and itself. A line of the header stands in every
         * declaration's source, so asked about in the first it is asked in front of the same text
         * it has in front of it in the whole file — and that is the only declaration whose source
         * would be its own text with the header written twice.
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
            List<Integer> from = new ArrayList<>(opens);
            from.set(0, 0);   // the first declaration is the header and itself
            for (int d = 0; d < from.size(); d++) {
                int to = d + 1 < from.size() ? from.get(d + 1) : lines.size();
                List<String> piece = lines.subList(from.get(d), to);
                pieces.add(piece);
                String alone = standing(d, header, String.join("\n", piece));
                CstParser.Result parsed = CstParser.parse(alone);
                // A declaration that will not stand on its own, or that the formatter writes
                // differently when it does, is one this cannot answer for. Its own canonical form
                // is recorded as absent and every candidate in it goes to the whole file.
                canonical.add(parsed.errors().isEmpty()
                        && Formatter.format(parsed.root()).equals(alone) ? alone : null);
            }
            return new Declarations(header, pieces, canonical, from);
        }

        /**
         * Declaration {@code d}, whose lines are {@code piece}, as a source of its own.
         *
         * <p>The first carries the header, and a source that has none — the corpus holds sources
         * that open with a declaration — puts nothing in front of any of them. Written as a blank
         * line instead, every declaration of those sources is a source the formatter writes
         * differently, and all of them go to the whole file.
         */
        private static String standing(int d, String header, String piece) {
            return d == 0 || header.isEmpty() ? piece : header + "\n" + piece;
        }

        /**
         * Which declaration line {@code i} is in, or -1 where this cannot answer for it.
         *
         * <p>Every line is in one, the first declaration beginning at line zero. What a declaration
         * cannot answer for is the first line of it and the last, where a blank line written in and
         * two lines run together reach the declaration next door — which is a question about the
         * file rather than about either of them.
         */
        private int at(int i) {
            int d = 0;
            while (d + 1 < opensAt.size() && i >= opensAt.get(d + 1)) {
                d++;
            }
            return canonical.get(d) == null ? -1 : d;
        }

        /**
         * Whether writing line {@code i} that way reaches the declaration after it.
         *
         * <p>Two of them do: a line run on into the next one, and a blank line written under it.
         * Written under the last line of a declaration, both are about what stands between two of
         * them, which is the file's question and not either declaration's. The rest write the line
         * where it stands.
         *
         * <p>What this buys is the refusal below being sound rather than any row: it is the local
         * question being a part of the whole one that the refusal rests on, and for these two it is
         * not.
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

        /**
         * What this says about writing line {@code i} that way, {@code local} being the
         * declaration it stands in written that way.
         */
        Locally says(String kind, String local, int i) {
            int d = at(i);
            if (d < 0 || local == null || reachesTheNextOne(kind, i, d)) {
                return new Locally.NotAsked();
            }
            String alone = standing(d, header, local);
            CstParser.Result parsed = CstParser.parse(alone);
            return parsed.errors().isEmpty()
                    && Formatter.format(parsed.root()).equals(canonical.get(d))
                    ? new Locally.Answered(alone)
                    : new Locally.Refused();
        }
    }

    /**
     * What the declaration a line stands in has to say about writing it that way.
     *
     * <p>Three answers rather than two. A declaration that refuses takes the candidate out; one
     * that answers hands back the same question asked of a twenty-first of the text; one that was
     * not asked leaves both to the whole file. Read as a yes and a no, the last would either drop a
     * candidate the whole file admits or carry a text nothing here checked the canonical form of.
     */
    private sealed interface Locally {

        /**
         * Nothing was asked, so the whole file answers both: a file of one declaration, a
         * declaration that does not stand on its own, and the ways of writing a line that reach the
         * declaration next door.
         */
        record NotAsked() implements Locally {}

        /** The declaration is not written that way either, so neither is the file. */
        record Refused() implements Locally {}

        /** The candidate cut to the declaration it is in. */
        record Answered(String text) implements Locally {}
    }

    /**
     * What each line of a canonical form is, in the terms the rules answer in.
     *
     * <p>Read from the layout and not from the characters. Two lines that open with the same word
     * at the same column can stand at boundaries three different rules answer for — one an
     * obligation broke, one a group settled, one a comment stands at — and a sweep that took them
     * for the same thing would ask about the first and drop the other two.
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
}
