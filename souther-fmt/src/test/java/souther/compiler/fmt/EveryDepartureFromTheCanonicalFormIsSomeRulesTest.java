package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import souther.compiler.cst.CstParser;
import souther.test.ClosedWorldContract;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source that departs from the canonical form departs at some rule's unit.
 *
 * <p>This is the check the whole issue rests on, and it is the one that cannot be written from the
 * rules: asked of the rules, a departure none of them holds is not a departure. So it is asked of
 * departures made from the text — one line of a canonical form written differently, for every way
 * of writing a line and every shape of line the corpus holds — and what is held is that the report
 * names each of them and names all of it.
 *
 * <p>The departures are written down beside this, as the smallest source each was found in, and
 * what is asked here is what the rules say of them. Finding them is a sweep of the corpus, and
 * that the ones written down are the ones the corpus has is
 * {@link TheDeparturesWrittenDownAreTheOnesTheCorpusHasTest}'s, which also says how they are found.
 * What is held of each one here is the rules' logic, and the departure it is held of is the least
 * text it was found in: the rest of the corpus says nothing more about it.
 */
@ClosedWorldContract
class EveryDepartureFromTheCanonicalFormIsSomeRulesTest {

    /** Where the departures are written down, beside this class. */
    static final String RECORDED = "every-departure-there-is.txt";

    /** One way of writing one shape of line differently, and the smallest source it was found in. */
    record Written(String kind, String shape, String text) {

        String pair() {
            return kind + " of " + shape;
        }
    }

    /**
     * A departure written down, and what the rules said about it.
     *
     * <p>The report is here rather than taken again by each check: {@link Deviations#of} is a
     * function of its text, and the checks over these rows ask for the same reports.
     */
    record Departure(String kind, String shape, String text, Deviations.Report report) {

        @Override
        public String toString() {
            return kind + " — " + shape;
        }
    }

    /** What was read and asked, so that the rows and the checks over all of them are one reading. */
    private static List<Departure> asked;

    static Stream<Departure> departures() {
        if (asked == null) {
            List<Departure> out = new ArrayList<>();
            for (Written each : recorded()) {
                out.add(new Departure(each.kind(), each.shape(), each.text(),
                        asked(each.pair(), each.text())));
            }
            asked = List.copyOf(out);
        }
        return asked.stream();
    }

    /**
     * What the rules say about one departure, with the row it was said about.
     *
     * <p>A departure the rules cannot answer at all ends the reading rather than one parameterized
     * test, and the test that would have been named it is never run — so the row is named here.
     */
    private static Deviations.Report asked(String pair, String text) {
        try {
            return Deviations.of(text);
        } catch (RuntimeException e) {
            throw new IllegalStateException(
                    "the rules could not answer about " + pair + ":\n" + text, e);
        }
    }

    /**
     * The departures written down: a header naming how long the source is, the way the line was
     * written and the shape of line it was, and then exactly that much of the source. A length
     * rather than a mark at the end, because a source can hold whatever a mark would be; the way
     * and the shape apart rather than as the pair, because a way can be written with the word the
     * pair is joined by.
     */
    static List<Written> recorded() {
        String all;
        try (InputStream in = EveryDepartureFromTheCanonicalFormIsSomeRulesTest.class
                .getResourceAsStream(RECORDED)) {
            assertNotNull(in, "the departures are not written down beside this: " + RECORDED);
            all = new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        List<Written> out = new ArrayList<>();
        int at = 0;
        while (at < all.length()) {
            int end = all.indexOf('\n', at);
            String header = all.substring(at, end);
            assertTrue(header.startsWith(HEADER), () -> "a departure begins with its header: "
                    + header);
            String[] said = header.substring(HEADER.length()).split(" \\| ", 3);
            int length = Integer.parseInt(said[0]);
            String text = all.substring(end + 1, end + 1 + length);
            out.add(new Written(said[1], said[2], text));
            at = end + 1 + length + 1;
        }
        return out;
    }

    private static final String HEADER = "=== ";

    /** {@code written} as {@link #recorded} reads it back. */
    static String writtenDown(List<Written> written) {
        StringBuilder out = new StringBuilder();
        for (Written each : written) {
            out.append(HEADER).append(each.text().length()).append(" | ").append(each.kind())
                    .append(" | ").append(each.shape()).append('\n').append(each.text())
                    .append('\n');
        }
        return out.toString();
    }

    /** One line of a canonical form, written the ways an author could have written it. */
    static Map<String, String> written(List<String> lines, int i) {
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

    /**
     * Each departure written down is one, and a rule names it and all of it.
     *
     * <p>That it is one is asked again here rather than trusted to the sweep that wrote it down:
     * the grammar and the formatter can change under a record, and a source that is now its own
     * canonical form, or no source at all, is a row that asks the rules nothing.
     */
    @ParameterizedTest(name = "{0}")
    @MethodSource("departures")
    void aDepartureIsNamedByARule(Departure departure) {
        CstParser.Result parsed = CstParser.parse(departure.text());
        assertEquals(List.of(), parsed.errors(), "the grammar admits it:\n" + departure.text());
        assertNotEquals(departure.text(), Formatter.format(parsed.root()),
                "it is not its own canonical form:\n" + departure.text());

        Deviations.Report report = departure.report();
        assertTrue(!report.deviations().isEmpty(),
                "no rule names it:\n" + departure.text());
        assertTrue(report.whole(),
                "what is named is not all of it: " + report.deviations() + "\n"
                        + departure.text());
    }

    /**
     * Every way of writing a line differently is among the departures written down.
     *
     * <p>A way no departure was written down for is a way the rules are never asked about here,
     * which a check over the rows would pass by having no row for it.
     */
    @Test
    void andEveryWayOfWritingALineDifferentlyIsAmongThem() {
        Set<String> kinds = new LinkedHashSet<>();
        departures().forEach(d -> kinds.add(d.kind()));

        assertEquals(written(List.of("    let f (a: Int): Int = a", "    let g = a"), 0).keySet(),
                kinds, "a way of writing a line that no departure was written down for");
    }
}
