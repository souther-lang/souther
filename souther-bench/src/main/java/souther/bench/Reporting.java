package souther.bench;

import souther.compiler.fmt.Deviations;

/**
 * How a report of what a source has against its canonical form grows with the source.
 *
 * <p>A report is asked round by round, and each round projects every rule's answer onto the text.
 * Two of those projections used to read the whole file to answer about one unit — which of a group's
 * places the source settled differently was found by sweeping every opportunity the layout has, and
 * which lines a level writes by walking every line the canonical form has. That costs the units a
 * source departs at multiplied by the file, and what says whether it is still there is a source that
 * departs at all of them.
 *
 * <p>The corpus does not have one. Real code departs from the canonical form at a handful of its
 * units however long it is, so the product stays inside the parse and a report over it is flat in
 * ms/KB whether the projection reads a unit or a file. So the sources here are generated with the
 * departure density held at every unit, and it is the size that moves — which is the axis the
 * product is in: a file twice as long has twice the units departing and twice the file to read them
 * from, and four times the cost if a unit's question is asked of the file.
 *
 * <p>Beside each is the same shape with one departure, at the same sizes. It is the control: a report
 * that is slow because the source is long is slow in both lines, and one that is slow because the
 * source departs everywhere is slow in the first alone. Reading the two together is what says which
 * of the file and the departures a number is about — the figure to read is not either line but the
 * distance between them, and whether that distance grows with the size.
 *
 * <p>The distance is in ms/KB rather than in ms, because a declaration written down the page is not
 * as many characters as the same declaration on one line: the two lines of a pair hold the same
 * declarations and not the same text, and reading their totals against each other would credit the
 * shorter one with the characters it does not have. The character count is beside each for that.
 *
 * <p>Two shapes, because the two projections are asked of different things and were fixed
 * separately. A group's is asked of a construct written down the page where the canonical form
 * writes it on one line; a level's is asked of a construct written where the canonical form writes
 * it and indented to the wrong column. Neither departs the other's way: the first has every line at
 * the column the canonical form would put it at, and the second breaks exactly where it does.
 */
final class Reporting {

    private Reporting() {}

    /**
     * Doubling, so the ratio between two lines names the exponent, and up to a size where the
     * product is not buried in the parse.
     *
     * <p>Two lists, because the two products have different constants and each has to be measured
     * where it can be seen. What a group's question costs at one opportunity is two searches of a
     * sorted run; what a level's costs at one line is a lookup, a substring and a walk of the
     * indent. So a level's product was four fifths of a report at two hundred declarations, and a
     * group's was a fifth of one at four hundred, a third at sixteen hundred and over half at
     * thirty-two hundred — each read as what the dense line has above its control, with the sweep
     * still in place.
     *
     * <p>Parsing a file and laying it out is linear in it and is the rest of a report, so a run that
     * stopped where the product is a fifth would show a ratio the noise covers.
     */
    private static final int[] GROUP_SIZES = {400, 800, 1600, 3200};

    /** The same, up to where a level's product is already the whole of the number. */
    private static final int[] LEVEL_SIZES = {200, 400, 800, 1600};

    static void measure(Report report) {
        for (int declarations : GROUP_SIZES) {
            line(report, declarations, "group, every", brokenGroups(declarations, declarations));
            line(report, declarations, "group, one", brokenGroups(declarations, 1));
        }
        for (int declarations : LEVEL_SIZES) {
            line(report, declarations, "level, every", wrongIndents(declarations, declarations));
            line(report, declarations, "level, one", wrongIndents(declarations, 1));
        }
    }

    private static void line(Report report, int declarations, String shape, String source) {
        Timing timing = Timing.of(2, 5, () -> Deviations.of(source));
        report.line("REPORT n=%-4d %-14s %6d chars %8.1f ms (%6.3f ms/KB)",
                declarations, shape, source.length(), timing.medianMillis(),
                timing.medianMillis() / (source.length() / 1024.0));
    }

    /**
     * {@code declarations} declarations, of which the first {@code broken} are written down the page
     * where the canonical form writes them on one line.
     *
     * <p>Each is its own group, so a source with every declaration broken departs from as many
     * decisions as it has declarations. The rest are written as the canonical form writes them, so
     * what separates one line of this measurement from another is how many of them departed and
     * nothing else about the file.
     */
    static String brokenGroups(int declarations, int broken) {
        StringBuilder out = new StringBuilder("module m\n\nlet g (a: Int, b: Int): Int = a + b\n");
        for (int i = 0; i < declarations; i++) {
            if (i < broken) {
                out.append("""

                        let f%d (a: Int): Int = g(
                            a,
                            a
                        )
                        """.formatted(i));
            } else {
                out.append("\nlet f%d (a: Int): Int = g(a, a)\n".formatted(i));
            }
        }
        return out.toString();
    }

    /**
     * {@code declarations} record types written down the page as the canonical form writes them, of
     * which the first {@code wrong} are indented two columns instead of four.
     *
     * <p>They break where the canonical form breaks, so no group decision is departed from and what
     * is left is the column. Each declaration is its own level, so a source with every one of them
     * indented wrongly departs at as many levels as it has declarations.
     */
    static String wrongIndents(int declarations, int wrong) {
        StringBuilder out = new StringBuilder("module m\n");
        for (int i = 0; i < declarations; i++) {
            String indent = i < wrong ? "  " : "    ";
            out.append("""

                    data D%d =
                    %s{ aRatherLongFieldName: Int
                    %s, anotherRatherLongFieldName: Int
                    %s, yetAnotherRatherLongFieldName: Int
                    %s}
                    """.formatted(i, indent, indent, indent, indent));
        }
        return out.toString();
    }
}
