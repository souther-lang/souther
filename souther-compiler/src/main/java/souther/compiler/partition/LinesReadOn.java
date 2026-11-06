package souther.compiler.partition;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.types.ApplicationsReadOn;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
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
 * ({@link #ofTheRelationsAbout}).
 *
 * <p>A place two different lines were read as says nothing of either: which applications read
 * which of them is not told by the place, so neither is said to be read on any
 * ({@link #notToldApart}). Nothing is made up for a line the place does not tell apart.
 *
 * @param byLine       the applications that read the line read as each place
 * @param notToldApart the places read as more than one line
 * @param byRelation   the applications that read each relation
 * @param asAWhole     the place whose line the comparison came to as a whole, where it came to one
 *                     line and no statement of several ({@link #ofTheComparison}), as the reading
 *                     that took it to be that line said
 */
record LinesReadOn(Map<PlaceOfALine, ApplicationsReadOn> byLine, Set<PlaceOfALine> notToldApart,
                   Map<UndividedByARelation, ApplicationsReadOn> byRelation,
                   Optional<PlaceOfALine> asAWhole) {

    /** Read once: on no application of a closure. */
    static final LinesReadOn NONE = new LinesReadOn(Map.of(), Set.of(), Map.of(), Optional.empty());

    LinesReadOn {
        byLine = Collections.unmodifiableMap(new LinkedHashMap<>(byLine));
        notToldApart = Set.copyOf(notToldApart);
        byRelation = Collections.unmodifiableMap(new LinkedHashMap<>(byRelation));
        Objects.requireNonNull(asAWhole, "the comparison came to one line, or to none");
    }

    /** The applications that read the line read as {@code place}: none where none did, or where
     *  the place was read as more than one line. */
    ApplicationsReadOn ofTheLine(PlaceOfALine place) {
        ApplicationsReadOn read = byLine.get(place);
        return read == null || notToldApart.contains(place) ? ApplicationsReadOn.NONE : read;
    }

    /**
     * The applications that read the line the comparison came to as a whole, which is the line of
     * the place the reading said it was ({@link #asAWhole}). None for a line drawn any other way
     * — on the runs a reading that stopped is read off, say — which is no line any application
     * was read as.
     */
    ApplicationsReadOn ofTheComparison() {
        return asAWhole.map(this::ofTheLine).orElse(ApplicationsReadOn.NONE);
    }

    /**
     * The applications that read a relation about {@code term}: what a line on the term parting
     * the values that settle the relations about it is read on. About it as the line is drawn
     * of them — every relation whose places hold the term's coordinate settles it alike
     * ({@code ComparisonAssessment.AgainstAnotherValue#settledByEvery}) — and no other.
     */
    ApplicationsReadOn ofTheRelationsAbout(NumericTerm term) {
        FilingCoordinate at = FilingCoordinate.of(term);
        ApplicationsReadOn out = ApplicationsReadOn.NONE;
        for (Map.Entry<UndividedByARelation, ApplicationsReadOn> each : byRelation.entrySet()) {
            if (each.getKey().places().contains(at)) {
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
        private PlaceOfALine asAWhole;

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

        /** The comparison came to the line read as {@code place}, as a whole: every application
         *  that read it drew that one line. */
        void asAWhole(PlaceOfALine place) {
            asAWhole = place;
        }

        LinesReadOn taken() {
            return new LinesReadOn(byLine, notToldApart, byRelation, Optional.ofNullable(asAWhole));
        }
    }
}
