package souther.compiler.fmt;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a canonical form has against the source it was made from.
 *
 * <p>Not a diff. The text differs at every boundary a decision moved, and a rule answers about its
 * own unit — so this attributes the differences to the units they came from and hands back one
 * witness per unit, which is what an author can act on.
 *
 * <p>One family at a time. The indentation rule is here; the others are added as each one's unit and
 * expectation become values.
 */
final class Witnesses {

    private Witnesses() {
    }

    /**
     * What the indentation rule has against {@code source}.
     *
     * <p>A level's column on each side. The canonical form's is what the layout wrote; the source's
     * is the column it put the same element in, found through the correspondence rather than by
     * counting lines in step — the two texts do not have the same lines, which is the point.
     *
     * <p>A level the source did not begin a line for is not answered here. What happened there is
     * that the source did not break where the canonical form does, which is the conditional or
     * forced layout rule's to report; asking this rule about it would have it name an indent for a
     * line nobody wrote.
     */
    static List<Witness> indentation(String source, Formatter.CanonicalForm canonical) {
        Layout layout = canonical.layout();
        Map<Doc.NestRef, Integer> written = new IdentityHashMap<>();
        Map<Doc.NestRef, Set<Integer>> had = new IdentityHashMap<>();
        Map<Integer, Place> opened = placesByStart(layout);

        for (Newline n : layout.breaks()) {
            if (n.under().isEmpty()) {
                continue;   // a line the file holds, at column zero, under no nesting
            }
            Doc.NestRef innermost = n.under().get(n.under().size() - 1);
            Integer already = written.put(innermost, n.indent());
            if (already != null && already != n.indent()) {
                throw new IllegalStateException(
                        "one level of nesting, written at column " + already + " and at column "
                                + n.indent() + "; a level has one column and the layout wrote two");
            }
            Integer column = sourceColumn(source, canonical,
                    opened.get(n.offset() + 1 + n.indent()), lineAfter(layout.text(), n));
            if (column != null) {
                had.computeIfAbsent(innermost, _ -> new LinkedHashSet<>()).add(column);
            }
        }

        List<Witness> out = new ArrayList<>();
        Set<Witness.Levels> seen = new LinkedHashSet<>();
        for (Newline n : layout.breaks()) {
            for (int i = 0; i < n.under().size(); i++) {
                Doc.NestRef inner = n.under().get(i);
                Doc.NestRef outer = i == 0 ? null : n.under().get(i - 1);
                Witness.Levels unit = new Witness.Levels(outer, inner);
                if (!seen.add(unit)) {
                    continue;
                }
                Integer step = step(written, outer, inner);
                Integer wrote = sourceStep(had, outer, inner);
                if (step != null && wrote != null && !step.equals(wrote)) {
                    out.add(new Witness.Indentation(unit, step, wrote));
                }
            }
        }
        return out;
    }

    /** How much further in the canonical form writes {@code inner} than {@code outer}, or null
     *  where either level has no line of its own for the rule to have written a column for. */
    private static Integer step(Map<Doc.NestRef, Integer> written, Doc.NestRef outer,
            Doc.NestRef inner) {
        Integer in = written.get(inner);
        Integer out = outer == null ? Integer.valueOf(0) : written.get(outer);
        return in == null || out == null ? null : in - out;
    }

    /** The same for the source, or null where it wrote either level in more than one column or in
     *  none. A level the source is not consistent about is not one step it got wrong. */
    private static Integer sourceStep(Map<Doc.NestRef, Set<Integer>> had, Doc.NestRef outer,
            Doc.NestRef inner) {
        Set<Integer> in = had.get(inner);
        Set<Integer> out = outer == null ? Set.of(0) : had.get(outer);
        if (in == null || out == null || in.size() != 1 || out.size() != 1) {
            return null;
        }
        return in.iterator().next() - out.iterator().next();
    }

    /** Which place each column of the canonical text opens, taking the widest where several begin
     *  together: the line belongs to what holds the rest of it. */
    private static Map<Integer, Place> placesByStart(Layout layout) {
        Map<Integer, Place> out = new LinkedHashMap<>();
        layout.extents().forEach((place, extent) -> {
            Place standing = out.get(extent.start());
            if (standing == null || layout.extents().get(standing).end() < extent.end()) {
                out.put(extent.start(), place);
            }
        });
        return out;
    }

    /** What the canonical form writes on the line {@code n} opens. */
    private static String lineAfter(String text, Newline n) {
        int from = n.offset() + 1;
        int to = text.indexOf('\n', from);
        return text.substring(from, to < 0 ? text.length() : to).stripLeading();
    }

    /**
     * How far in the source wrote the line it holds {@code place} on, or null where it did not
     * begin a line with it.
     *
     * <p>The element is not always the first thing on that line. A match arm's {@code |} is written
     * by the canonical form's place and is the match expression's own token in the source, so a
     * source that broke before the arm has the bar in front of the node the place was written from.
     * What is asked is therefore whether the source's line begins the way the canonical one does up
     * to the element — which a line the source ran on into does not: a {@code let} the source left
     * after an opening brace has that brace in front of it, and the canonical line for it has not.
     */
    private static Integer sourceColumn(String source, Formatter.CanonicalForm canonical,
            Place place, String canonicalLine) {
        if (place == null) {
            return null;
        }
        List<Written> from = canonical.construction().places().sourcesOf(place);
        if (from.size() != 1) {
            return null;   // written from nothing, or from several elements that are not one column
        }
        int start = from.get(0).start();
        if (start > source.length()) {
            return null;
        }
        int lineStart = source.lastIndexOf('\n', Math.max(0, start - 1)) + 1;
        String before = source.substring(lineStart, start).strip();
        if (!before.isEmpty() && !canonicalLine.startsWith(before)) {
            return null;   // the source ran on into this line rather than opening one for it
        }
        int indent = 0;
        while (lineStart + indent < source.length() && source.charAt(lineStart + indent) == ' ') {
            indent++;
        }
        return indent;
    }
}
