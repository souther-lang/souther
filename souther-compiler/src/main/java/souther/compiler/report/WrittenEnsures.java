package souther.compiler.report;

import souther.compiler.ast.Hir;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.Region;
import souther.compiler.query.Answer;
import souther.compiler.query.Bodies;
import souther.compiler.query.Db;
import souther.compiler.query.Front;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a behavior has written in its {@code ensures}, in the author's own words.
 *
 * <p>Cut out of the source and not printed from what the clause was read to mean. The two are
 * different things and only one of them is what a reader is owed here: a clause the author wrote is
 * text, and a rule the checker holds is that text resolved, typed and specialized per case
 * ({@link souther.compiler.check.BehaviorContract}). Rendering the second would hand back the
 * compiler's equivalent words for the author's, and the day a normalization changed one of them the
 * quote would move without anybody editing anything.
 *
 * <p>Read off the settled module and not off the contracts, which is the same decision seen from the
 * other side. A contract is a clause the checker could read: {@link Bodies.Contracts} takes each
 * behavior's reading on its own and drops the ones that were refused, so a behavior carrying a clause
 * this compiler would not accept has no entry there. {@code souther examples} says what is wrong with
 * the source and then reports what it observed, so that behavior's rows are offered anyway — a
 * behavior whose arm names a data that is no case of its answer is refused and still gets a row per
 * case of a sum it takes. A quote taken from the contracts would print nothing over those rows, which
 * reads as a behavior that states nothing rather than one whose statement was refused. The words are
 * on the page either way, and that is the whole of what the heading claims.
 */
final class WrittenEnsures {

    /**
     * The clauses of each behavior of {@code module}, keyed by the name the behavior is declared
     * under, in the order they are written. A behavior carrying none is not in the map.
     *
     * <p>All of a behavior's clauses or none of them. A behavior a pass wrote carries positions in
     * no text anybody holds, and half a list under a heading saying what was written would say the
     * clauses it could not cut were not there.
     */
    static Map<String, List<String>> of(Db db, String module) {
        Answer<Hir.Module> settled = db.ask(new Bodies.Settled(module));
        if (!settled.present()) {
            return Map.of();
        }
        Map<String, List<String>> out = new LinkedHashMap<>();
        for (Hir.BehaviorDef behavior : settled.value().behaviors()) {
            if (!(behavior instanceof Hir.SpecBehavior spec) || spec.ensures().isEmpty()) {
                continue;
            }
            List<String> written = quoted(db, spec);
            if (written != null) {
                out.put(spec.name(), written);
            }
        }
        return out;
    }

    /** Every clause of one behavior as it is written, or nothing where one of them is in a text this
     *  compile cannot quote. */
    private static List<String> quoted(Db db, Hir.SpecBehavior spec) {
        List<String> out = new ArrayList<>();
        for (Hir.EnsuresClause clause : spec.ensures()) {
            if (!(clause.pos().quotedFrom()
                    instanceof QuotedFrom.ASourceThisCompileHolds(SourceId source))) {
                return null;
            }
            Answer<String> text = db.ask(new Front.Text(source));
            if (!text.present()) {
                return null;
            }
            String cut = cut(text.value(), clause.region());
            if (cut == null) {
                return null;
            }
            out.add(cut);
        }
        return List.copyOf(out);
    }

    /**
     * The characters {@code region} covers, with the indentation the declaration sits at taken off
     * the lines under the first.
     *
     * <p>A clause begins at the {@code ensures} keyword, so the first line of the cut carries none of
     * that indentation and the rest carry all of it. Taking the start column off the others is what
     * keeps a clause written over several lines the shape its author gave it — the arms stay where
     * they were put relative to the keyword — while letting the block indent the whole of it as one.
     */
    private static String cut(String text, Region region) {
        if (region == null) {
            return null;
        }
        List<String> lines = text.lines().toList();
        int first = region.start().line();
        int last = region.end().line();
        if (first < 1 || last > lines.size() || first > last) {
            return null;
        }
        int declaredAt = region.start().column() - 1;
        StringBuilder out = new StringBuilder();
        for (int n = first; n <= last; n++) {
            String line = lines.get(n - 1);
            int from = n == first ? declaredAt : Math.min(declaredAt, indentOf(line));
            int to = n == last ? region.end().column() - 1 : line.length();
            if (from > line.length() || to > line.length() || to < from) {
                return null;
            }
            out.append(line, from, to);
            if (n < last) {
                out.append('\n');
            }
        }
        return out.toString();
    }

    private static int indentOf(String line) {
        int i = 0;
        while (i < line.length() && Character.isWhitespace(line.charAt(i))) {
            i++;
        }
        return i;
    }

    private WrittenEnsures() {}
}
