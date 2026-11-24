package souther.compiler.partition;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.AuthoredPointMapping;
import souther.compiler.types.ApplicationsReadOn;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

/**
 * Which applications of the closures a comparison stands in read each line it drew and each
 * relation it stated, as one reading of the comparison tells them: a line by what it is, and a
 * relation by itself.
 *
 * <p>Beside the lines and never in them. A line is one line however many applications draw it,
 * and every reader that tells two lines apart, files one, or keeps one of two alike asks what the
 * line is; held in the line, which applications read it would be part of each of those answers.
 * Held here, it is asked of what it is about, by what tells that apart, and nowhere else.
 *
 * <p>What a line is, is what the reading put each application's line together by: the place of
 * its author's line it is read as, where it is cut and how it stands to that line
 * ({@link DrawnLine}) — which is what a line's origin is made of again where it is drawn. Two
 * lines at one place are two lines, each read on what read it.
 *
 * <p>Of each line and of each relation, and not of the comparison. A relation is a line of none
 * of the author's, and the lines parting the values that settle it are drawn where the relations
 * about a number settle it, so each is read on what read those relations and no other
 * ({@link #ofTheRelationsAbout}).
 *
 * @param byLine     the applications that read each line
 * @param byRelation the applications that read each relation
 * @param asAWhole   the line the comparison came to as a whole, where it came to one line and no
 *                   statement of several ({@link #ofTheComparison}), as the reading that took it
 *                   to be that line said
 */
record LinesReadOn(Map<DrawnLine, ApplicationsReadOn> byLine,
                   Map<UndividedByARelation, ApplicationsReadOn> byRelation,
                   Optional<DrawnLine> asAWhole) {

    /** Read once: on no application of a closure. */
    static final LinesReadOn NONE = new LinesReadOn(Map.of(), Map.of(), Optional.empty());

    LinesReadOn {
        byLine = Collections.unmodifiableMap(new LinkedHashMap<>(byLine));
        byRelation = Collections.unmodifiableMap(new LinkedHashMap<>(byRelation));
        Objects.requireNonNull(asAWhole, "the comparison came to one line, or to none");
    }

    /**
     * One line a comparison drew, as the reading told one application's line from another's:
     * the place of the author's line it is read as, the cut, and how it stands to the author's
     * line.
     */
    record DrawnLine(PlaceOfALine place, Cutting cutting, AuthoredPointMapping authored) {

        DrawnLine {
            Objects.requireNonNull(place, "a line is read as some place");
            Objects.requireNonNull(cutting, "and cut somewhere");
            Objects.requireNonNull(authored, "and stands to its author's line some way");
        }
    }

    /** The applications that read the line drawn on {@code cutting}, standing to its author's
     *  line as {@code authored} says, read as {@code place}: none where none did. */
    ApplicationsReadOn ofTheLine(PlaceOfALine place, Cutting cutting,
                                 AuthoredPointMapping authored) {
        return byLine.getOrDefault(new DrawnLine(place, cutting, authored),
                ApplicationsReadOn.NONE);
    }

    /**
     * The applications that read the line the comparison came to as a whole ({@link #asAWhole}),
     * where it is the one drawn on {@code cutting} as {@code authored} says. None for a line drawn
     * any other way — on the runs a reading that stopped is read off, say — which is no line any
     * application was read as.
     */
    ApplicationsReadOn ofTheComparison(Cutting cutting, AuthoredPointMapping authored) {
        return asAWhole.filter(line -> line.cutting().equals(cutting)
                        && line.authored().equals(authored))
                .map(line -> byLine.getOrDefault(line, ApplicationsReadOn.NONE))
                .orElse(ApplicationsReadOn.NONE);
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

        private final Map<DrawnLine, ApplicationsReadOn> byLine = new LinkedHashMap<>();
        private final Map<UndividedByARelation, ApplicationsReadOn> byRelation =
                new LinkedHashMap<>();
        private DrawnLine asAWhole;

        /** {@code line}, read as {@code place}, read by {@code by}: the line, where it is one
         *  drawn, and each relation it states, where it is a relation to another value. What is
         *  neither draws nothing a reading of it is owed. */
        void read(PlaceOfALine place, Cutting.Read line, ApplicationsReadOn by) {
            switch (line) {
                case Cutting.Read.Cuts cuts -> byLine.merge(
                        new DrawnLine(place, cuts.cutting(), cuts.authored()), by,
                        ApplicationsReadOn::and);
                case Cutting.Read.AgainstAnotherValue against ->
                        against.relations().forEach(relation ->
                                byRelation.merge(relation, by, ApplicationsReadOn::and));
                case Cutting.Read.CutsNothing _, Cutting.Read.AnswersNowhere _,
                     Cutting.Read.StatesNoRelation _, Cutting.Read.Stopped _,
                     Cutting.Read.NoOrderToCountOn _, Cutting.Read.NumberNoRatioHolds _,
                     Cutting.Read.Several _ -> { }
            }
        }

        /** The comparison came to {@code line}, read as {@code place}, as a whole: every
         *  application that read it drew that one line. */
        void asAWhole(PlaceOfALine place, Cutting.Read line) {
            if (line instanceof Cutting.Read.Cuts cuts) {
                asAWhole = new DrawnLine(place, cuts.cutting(), cuts.authored());
            }
        }

        LinesReadOn taken() {
            return new LinesReadOn(byLine, byRelation, Optional.ofNullable(asAWhole));
        }
    }
}
