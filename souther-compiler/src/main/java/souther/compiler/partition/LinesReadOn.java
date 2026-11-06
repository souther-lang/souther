package souther.compiler.partition;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.types.ApplicationsReadOn;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

/**
 * Which applications of the closures a comparison stands in read each line it drew and each
 * relation it stated, as one reading of the comparison tells them: a line by the place of its
 * author's line it was read as, and a relation by itself.
 *
 * <p>Beside the lines and never in them. A line is one line however many applications draw it,
 * and every reader that tells two lines apart, files one, or keeps one of two alike asks what the
 * line is; held in the line, which applications read it would be part of each of those answers.
 * Held here, it is asked of what it is about, by what tells that apart, and nowhere else.
 *
 * <p>Of each line and of each relation, and not of the comparison. A relation is a line of none
 * of the author's, and the lines parting the values that settle it are drawn where the relations
 * about a number settle it, so each is read on what read those relations and no other
 * ({@link #ofTheRelationsAt}).
 *
 * <p>A place two different lines were read as says nothing of either: which applications read
 * which of them is not told by the place, so neither is said to be read on any
 * ({@link #notToldApart}). Nothing is made up for a line the place does not tell apart.
 *
 * @param byLine       the applications that read the line read as each place
 * @param notToldApart the places read as more than one line
 * @param byRelation   the applications that read each relation
 */
record LinesReadOn(Map<PlaceOfALine, ApplicationsReadOn> byLine, Set<PlaceOfALine> notToldApart,
                   Map<UndividedByARelation, ApplicationsReadOn> byRelation) {

    /** Read once: on no application of a closure. */
    static final LinesReadOn NONE = new LinesReadOn(Map.of(), Set.of(), Map.of());

    LinesReadOn {
        byLine = Collections.unmodifiableMap(new LinkedHashMap<>(byLine));
        notToldApart = Set.copyOf(notToldApart);
        byRelation = Collections.unmodifiableMap(new LinkedHashMap<>(byRelation));
    }

    /** The applications that read the line read as {@code place}: none where none did, or where
     *  the place was read as more than one line. */
    ApplicationsReadOn ofTheLine(PlaceOfALine place) {
        ApplicationsReadOn read = byLine.get(place);
        return read == null || notToldApart.contains(place) ? ApplicationsReadOn.NONE : read;
    }

    /**
     * The applications that read the one line the comparison drew, where it drew one that is
     * none of its parts: every application drew it, so it is the one line told. None where the
     * lines told are not one.
     */
    ApplicationsReadOn ofTheComparison() {
        return byLine.size() == 1 && notToldApart.isEmpty()
                ? byLine.values().iterator().next() : ApplicationsReadOn.NONE;
    }

    /**
     * The applications that read a relation about one of {@code over}: what a line on those
     * numbers parting the values that settle the relations about them is read on.
     */
    ApplicationsReadOn ofTheRelationsAt(Collection<FilingCoordinate> over) {
        ApplicationsReadOn out = ApplicationsReadOn.NONE;
        for (Map.Entry<UndividedByARelation, ApplicationsReadOn> each : byRelation.entrySet()) {
            if (!Collections.disjoint(each.getKey().places(), over)) {
                out = out.and(each.getValue());
            }
        }
        return out;
    }

    /** What one reading of a comparison is told, line by line, as it reads each application. */
    static final class Taking {

        private final Map<PlaceOfALine, ApplicationsReadOn> byLine = new LinkedHashMap<>();
        private final Map<PlaceOfALine, Cutting.Read> lineOf = new HashMap<>();
        private final Set<PlaceOfALine> notToldApart = new HashSet<>();
        private final Map<UndividedByARelation, ApplicationsReadOn> byRelation =
                new LinkedHashMap<>();

        /** {@code line}, read as {@code place}, read by {@code by}; and each relation it states,
         *  where it is a relation to another value, read by them too. */
        void read(PlaceOfALine place, Cutting.Read line, ApplicationsReadOn by) {
            Cutting.Read before = lineOf.putIfAbsent(place, line);
            if (before != null && !before.equals(line)) {
                notToldApart.add(place);
            }
            byLine.merge(place, by, ApplicationsReadOn::and);
            if (line instanceof Cutting.Read.AgainstAnotherValue against) {
                against.relations().forEach(relation ->
                        byRelation.merge(relation, by, ApplicationsReadOn::and));
            }
        }

        LinesReadOn taken() {
            return new LinesReadOn(byLine, notToldApart, byRelation);
        }
    }
}
