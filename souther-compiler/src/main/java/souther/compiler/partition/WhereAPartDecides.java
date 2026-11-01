package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.CasesHeldTo;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.stream.Collectors;

/**
 * One of the lines a statement of several relations draws, read in one case of where the statement
 * turns on it.
 *
 * <p>The two together because the second is part of what the line is. {@code Int.max(a, b) <= g}
 * turns on {@code a = g} only where {@code b <= g}, so a row at that line with {@code b} above
 * {@code g} is answered the same way on both sides of it: it stands at the line and says nothing
 * about it. A reader holding the line without where it decides would take that row for one that
 * met it.
 *
 * <p>One case and not all of them. Where a line decides may be one of several things, and each is
 * somewhere a row can be composed to be; the line is read once in each, and a row meets it in any.
 *
 * @param part    which of the author's lines this is a place of, and which place
 * @param decides the case: parts of the statement that hold together beside the line, where
 *                crossing it turns the statement round. Over the relations the statement holds,
 *                every one of them a relation over the input's own numbers — so a row's values say
 *                whether it holds
 * @param besideOtherLines whether the statement draws other lines on the input space, so a point
 *                named by its values may be a point of any of them and the relations of the case
 *                are what tells this line's apart ({@link #said})
 */
public record WhereAPartDecides(PlaceOfALine part, Proposition decides,
                                boolean besideOtherLines) {

    public WhereAPartDecides {
        Objects.requireNonNull(part, "a line of a statement is one of its lines");
        Objects.requireNonNull(decides, "a line decides somewhere, or nowhere");
    }

    /** A line that is alone in its statement, or read where that is not known. */
    public WhereAPartDecides(PlaceOfALine part, Proposition decides) {
        this(part, decides, false);
    }

    /** The line and where it decides. Whether other lines are beside it is how it is said and not
     *  which reading it is, so a reading is found by the same key whichever way it was made. */
    @Override
    public boolean equals(Object other) {
        return other instanceof WhereAPartDecides that && part.equals(that.part)
                && decides.equals(that.decides);
    }

    @Override
    public int hashCode() {
        return Objects.hash(part, decides);
    }

    /**
     * Where the line decides, as a report says it after what a row there has to do on the
     * positions {@code readAt} — or null where that says all of it.
     *
     * <p>Said because it is part of the line. Two readings of one comparison at one place can be
     * readings of two lines in two cases, and the place and the values alone tell a reader nothing
     * about which a row of theirs is at: {@code month.value <= minimum(term)} asks for a month above
     * 12 where {@code term} is {@code OneYear} and for one above 24 where it is {@code TwoYear}.
     *
     * <p>The cases of values the line decides in: which case a value is, whether it holds a value,
     * which truth it is. Where the statement has other readings beside this one, the relations
     * the case holds of the quantity the point is at too, since the values of the point do not say
     * which of two lines drawn on one quantity in different cases a point is on. Written as the
     * statement states them and in its structure: {@code and} and {@code or} as they join the
     * parts, with parentheses where one is inside the other. A relation over other numbers, or a
     * line alone in its statement, is said by the values a search composes against; written out
     * as well, a reader is shown how the statement was taken apart — a part read once held and
     * once failing where one of them is enough — and not anything a row has to do.
     *
     * <p>What every row in the case is, read through the whole of it ({@link CasesHeldTo}): a case
     * said as one of several things is where each of them holds, and what they all hold a value
     * to is what the case does. Parts that state no relation are said that way together.
     *
     * <p>Less what the positions already say. A line at a field of one case of a value decides
     * where the value is that case, and the position it is read at is named through that case.
     */
    public String said(List<TermPath> readAt) {
        return besideOtherLines ? said(decides, readAt) : casesSaid(decides, readAt);
    }

    private static String said(Proposition stated, List<TermPath> readAt) {
        if (!statesARelation(stated)) {
            return casesSaid(stated, readAt);
        }
        return switch (stated) {
            case Proposition.Compared compared -> onlyAtThePoint(compared, readAt)
                    ? relationSaid(compared) : null;
            case Proposition.OfTheWays ways -> said(ways.written(), readAt);
            case Proposition.WhereItAnswers where ->
                    allSaid(List.of(where.answers(), where.states()), readAt);
            case Proposition.All all -> allSaid(all.parts(), readAt);
            case Proposition.Any any -> {
                List<String> ways = new ArrayList<>();
                for (Proposition way : any.parts()) {
                    String said = said(way, readAt);
                    if (said == null) {
                        yield null;
                    }
                    ways.add(parenthesizedIfJoined(way, said));
                }
                yield String.join(" or ", ways);
            }
            default -> casesSaid(stated, readAt);
        };
    }

    /** What each part says, joined by {@code and}: a part that says nothing leaves the rest. */
    private static String allSaid(List<Proposition> parts, List<TermPath> readAt) {
        List<String> said = new ArrayList<>();
        for (Proposition part : parts) {
            String partSaid = said(part, readAt);
            if (partSaid != null) {
                said.add(parenthesizedIfJoined(part, partSaid));
            }
        }
        return said.isEmpty() ? null : String.join(" and ", said);
    }

    /**
     * Whether {@code compared} is over the one quantity the point is at and nothing else. A
     * relation over other numbers is not what tells two lines on this quantity apart, and said
     * beside them it shows how the statement was taken apart.
     */
    private static boolean onlyAtThePoint(Proposition.Compared compared, List<TermPath> readAt) {
        if (readAt.size() != 1) {
            return false;
        }
        Set<Quantity> atoms = switch (compared.relation()) {
            case Relation.Affine affine -> affine.form().coefs().keySet();
            case Relation.Ordered ordered -> Set.of(ordered.term());
        };
        return atoms.stream().allMatch(atom -> atom instanceof DecisionAtom.OfTheInput input
                && input.term().subjectPath().equals(readAt.getFirst()));
    }

    private static String parenthesizedIfJoined(Proposition part, String said) {
        return part instanceof Proposition.All || part instanceof Proposition.Any
                ? "(" + said + ")" : said;
    }

    /** Whether a relation between numbers is somewhere in what {@code stated} is made of. */
    private static boolean statesARelation(Proposition stated) {
        return stated instanceof Proposition.Compared
                || (isMadeOfParts(stated)
                && stated.partsHeld().stream().anyMatch(WhereAPartDecides::statesARelation));
    }

    /** Whether the parts of {@code stated} are the statement and not what it counts. */
    private static boolean isMadeOfParts(Proposition stated) {
        return stated instanceof Proposition.All || stated instanceof Proposition.Any
                || stated instanceof Proposition.WhereItAnswers
                || stated instanceof Proposition.OfTheWays;
    }

    /** The relation as the statement states it: {@code form rel 0} or its denial, with the
     *  constant moved to the right. */
    private static String relationSaid(Proposition.Compared compared) {
        return switch (compared.relation()) {
            case Relation.Affine affine -> {
                Rel states = compared.holds() ? affine.proposition()
                        : affine.proposition().denied();
                yield sumSaid(affine.form()) + " " + states.written() + " "
                        + affine.form().constant().negated().spelled();
            }
            case Relation.Ordered ordered -> {
                Rel states = compared.holds() ? ordered.proposition()
                        : ordered.proposition().denied();
                yield ordered.term().spelled() + " " + states.written() + " "
                        + ordered.at().spelled();
            }
        };
    }

    /** The terms of {@code form}, without its constant, in the order the atoms are spelled. */
    private static String sumSaid(LinearForm<Quantity> form) {
        Map<String, ExactRatio> byName = new TreeMap<>();
        form.coefs().forEach((atom, weight) -> byName.put(atom.spelled(), weight));
        StringBuilder out = new StringBuilder();
        byName.forEach((name, weight) -> {
            boolean first = out.isEmpty();
            ExactRatio size = weight.signum() < 0 ? weight.negated() : weight;
            String term = size.equals(ExactRatio.ONE) ? name : size.spelled() + " * " + name;
            if (first) {
                out.append(weight.signum() < 0 ? "-" : "").append(term);
            } else {
                out.append(weight.signum() < 0 ? " - " : " + ").append(term);
            }
        });
        return out.toString();
    }

    private static String casesSaid(Proposition stated, List<TermPath> readAt) {
        List<String> said = new ArrayList<>();
        CasesHeldTo.of(stated).forEach((at, held) -> {
            switch (held) {
                case CasesHeldTo.Held.OneOf(var cases) -> {
                    if (readAt.stream().noneMatch(each -> each.isAtOrUnder(at.refine(cases)))) {
                        said.add(at + " is " + spelled(cases));
                    }
                }
                case CasesHeldTo.Held.NoneOf(var cases) -> said.add(at + " is not "
                        + spelled(cases));
                case CasesHeldTo.Held.ATruth(var holds) -> said.add(at + " is " + holds);
            }
        });
        return said.isEmpty() ? null : String.join(" and ", said);
    }

    private static String spelled(CasesLeft cases) {
        return cases.atoms().stream().map(Refinement::spelled).collect(Collectors.joining(" or "));
    }

    /** Whether a row is somewhere the line decides, or what kept that from being read. */
    sealed interface AtARow {

        /** The row is somewhere the statement turns on the line. */
        record Decides() implements AtARow {}

        /** The row is somewhere the statement does not turn on the line, or holds no value one of
         *  the relations is over. */
        record DecidesNothing() implements AtARow {}

        /** A number the relations are over could not be read at the row, for these reasons. */
        record CouldNotTell(Set<ReadingGap> why) implements AtARow {

            /** In the order the reasons were met, which is the order a reader is told them in. */
            public CouldNotTell {
                why = Collections.unmodifiableSet(new LinkedHashSet<>(why));
            }
        }

        AtARow DECIDES = new Decides();

        AtARow DECIDES_NOTHING = new DecidesNothing();
    }

    /**
     * This, put to rows: each relation it is over, as the quantity a row is read at.
     *
     * @param subject the input the rows are of, whose reading says which order each number is on
     */
    AskedOfRows askedOfRows(String behavior, MeasuredInput subject) {
        return new AskedOfRows(subject.putToRows(decides, behavior),
                subject.putToRowsAtSomeElement(decides, behavior));
    }

    /** Where a line decides, ready to be asked of rows. */
    static final class AskedOfRows {

        private final AStatementAtARow decides;
        /** The same, asked at some element of a list of whole numbers it weighs, where it weighs
         *  one: what a row is asked then. */
        private final Optional<ACaseAskedAtSomeElement> atSomeElement;

        private AskedOfRows(AStatementAtARow decides,
                            Optional<ACaseAskedAtSomeElement> atSomeElement) {
            this.decides = decides;
            this.atSomeElement = atSomeElement;
        }

        /** Reads {@code row} the way {@link #at} does, for the walk that finds which containers a
         *  row has to choose an element of ({@link AStatementAtARow#lookAt}). */
        void lookAt(BorderQuantity.Observation row) {
            decides.lookAt(row);
        }

        /**
         * Whether {@code row} is somewhere the line decides, read off its own numbers.
         *
         * <p>A relation over a position the row wrote nothing at holds of no value there, so the
         * row is not somewhere it holds.
         */
        AtARow at(BorderQuantity.Observation row) {
            return switch (atSomeElement.map(asked -> asked.at(row)).orElseGet(() ->
                    decides.at(row))) {
                case AStatementAtARow.Answer.Holds _ -> AtARow.DECIDES;
                case AStatementAtARow.Answer.Fails _ -> AtARow.DECIDES_NOTHING;
                case AStatementAtARow.Answer.CouldNotTell(var why) -> new AtARow.CouldNotTell(why);
            };
        }
    }
}
