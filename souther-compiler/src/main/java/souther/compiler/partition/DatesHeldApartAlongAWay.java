package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;

/**
 * What a way says of the places it names, as the sets of places it ties together, and which of
 * those sets some dates hold everything the way says of: a fact of the way, asked once for it and
 * read by each side shown along it.
 *
 * <p>Two places are tied where one statement or one narrowing of the way reads both, where one is
 * at or under the other, or through a place tied to each. What a statement reads is what each of
 * its numbers is read off ({@link NumericTerm#placesReadOff}): a product reads every place of
 * either factor, and a number taken with arguments the places of those too, so no number is read
 * as fewer places than it turns on.
 *
 * <p>A set is held where every statement and narrowing reading a place of it is a form of parts
 * of dates the declarations leave every date, or every date between its ends, and some dates hold
 * them all ({@link DatesThatHoldEveryStatement}). Anything else read there is not asked of the
 * calendar, and the set is not held.
 */
final class DatesHeldApartAlongAWay {

    private final List<UndividedByARelation.OnAWay> conditions;
    private final List<TakenConstraint> narrowing;
    private final Function<NumericTerm.TakenOf, DateTranslation> daysOf;
    private final Map<TermPath, TermPath> above = new LinkedHashMap<>();
    /** Whether some dates hold each set, by the place it is filed under, once asked. */
    private final Map<TermPath, Boolean> held = new LinkedHashMap<>();

    private DatesHeldApartAlongAWay(List<UndividedByARelation.OnAWay> conditions,
                                    List<TakenConstraint> narrowing,
                                    Function<NumericTerm.TakenOf, DateTranslation> daysOf) {
        this.conditions = conditions;
        this.narrowing = narrowing;
        this.daysOf = daysOf;
    }

    /**
     * The sets of places {@code conditions} and {@code narrowing} tie, among them the places
     * {@code alsoNamed} are read off, which nothing need state.
     *
     * @param daysOf the dates the declarations leave the date a part is taken of, as the days a
     *               move by nothing is defined at, or null where they leave it anything else
     */
    static DatesHeldApartAlongAWay of(List<UndividedByARelation.OnAWay> conditions,
                                      List<TakenConstraint> narrowing,
                                      Collection<TermPath> alsoNamed,
                                      Function<NumericTerm.TakenOf, DateTranslation> daysOf) {
        DatesHeldApartAlongAWay out = new DatesHeldApartAlongAWay(conditions, narrowing, daysOf);
        alsoNamed.forEach(place -> out.above.putIfAbsent(place, place));
        for (UndividedByARelation.OnAWay each : conditions) {
            out.tieAll(placesOf(each));
        }
        for (TakenConstraint each : narrowing) {
            out.tieAll(placesReadOff(each.terms()));
        }
        List<TermPath> places = List.copyOf(out.above.keySet());
        for (TermPath one : places) {
            for (TermPath other : places) {
                if (!one.equals(other) && (one.bearsOn(other) || other.bearsOn(one))) {
                    out.tie(one, other);
                }
            }
        }
        return out;
    }

    /** Every place {@code terms} are read off, in order, each once. */
    static Set<TermPath> placesReadOff(Collection<NumericTerm> terms) {
        Set<TermPath> out = new LinkedHashSet<>();
        terms.forEach(term -> out.addAll(term.placesReadOff()));
        return out;
    }

    /** Every place {@code statement} turns on, and every place a number it relates is read off. */
    private static Set<TermPath> placesOf(UndividedByARelation.OnAWay statement) {
        Set<TermPath> out = new LinkedHashSet<>(statement.positions());
        TakenConstraint.Affine affine = statement.affine();
        if (affine != null) {
            out.addAll(placesReadOff(affine.form().coefs().keySet()));
        }
        return out;
    }

    /**
     * The places tied to {@code place}, where none of them is tied to a place of {@code side} and
     * some dates hold everything the way says of them — or empty, where the side is tied to it,
     * no dates are found to hold it, and the way may then have no row at all, or either is a
     * place the way was not told of.
     */
    Optional<Set<TermPath>> heldApartFrom(NumericTerm side, TermPath place) {
        if (!above.containsKey(place)) {
            return Optional.empty();
        }
        for (TermPath ofTheSide : side.placesReadOff()) {
            if (!above.containsKey(ofTheSide) || top(ofTheSide).equals(top(place))) {
                return Optional.empty();
            }
        }
        return held.computeIfAbsent(top(place), this::someDatesHold)
                ? Optional.of(tiedTo(place)) : Optional.empty();
    }

    /** The places the way ties to {@code place}, itself among them; none where the way was not
     *  told of it. */
    Set<TermPath> tiedTo(TermPath place) {
        Set<TermPath> out = new LinkedHashSet<>();
        if (above.containsKey(place)) {
            TermPath filed = top(place);
            for (TermPath each : above.keySet()) {
                if (top(each).equals(filed)) {
                    out.add(each);
                }
            }
        }
        return out;
    }

    /**
     * Whether some dates hold every statement and narrowing of the way reading the set filed under
     * {@code filed}. Every place one of them reads is tied to the others it reads, so each is of
     * one set, and the set of any place it reads is the set it is of.
     */
    private boolean someDatesHold(TermPath filed) {
        List<TakenConstraint.Affine> stated = new ArrayList<>();
        for (UndividedByARelation.OnAWay statement : conditions) {
            if (isOf(placesOf(statement), filed)) {
                if (statement.affine() == null) {
                    return false;
                }
                stated.add(statement.affine());
            }
        }
        for (TakenConstraint each : narrowing) {
            if (isOf(placesReadOff(each.terms()), filed)) {
                if (!(each instanceof TakenConstraint.Affine affine)) {
                    return false;
                }
                stated.add(affine);
            }
        }
        return someDatesHoldAll(stated);
    }

    private boolean isOf(Set<TermPath> read, TermPath filed) {
        return !read.isEmpty() && top(read.iterator().next()).equals(filed);
    }

    /**
     * Whether some dates hold every one of {@code statements}: false where a term of one is
     * anything but a part of a date the declarations leave every date, or every date between its
     * ends, or a weight or a constant is not a whole number.
     */
    private boolean someDatesHoldAll(List<TakenConstraint.Affine> statements) {
        Map<TermPath, Integer> dates = new LinkedHashMap<>();
        List<DateTranslation> days = new ArrayList<>();
        List<DatesThatHoldEveryStatement.Statement> asked = new ArrayList<>();
        for (TakenConstraint.Affine each : statements) {
            Map<DatesThatHoldEveryStatement.Part, Long> parts = new LinkedHashMap<>();
            for (Map.Entry<NumericTerm, ExactRatio> term : each.form().coefs().entrySet()) {
                if (!(term.getKey() instanceof NumericTerm.TakenOf taken)
                        || !(taken.takenAs() instanceof TakenAs.PartOfDate(
                                TakenAs.DatePart part))) {
                    return false;
                }
                Integer date = dates.get(taken.position());
                if (date == null) {
                    DateTranslation ofIt = daysOf.apply(taken);
                    if (ofIt == null) {
                        return false;
                    }
                    date = dates.size();
                    dates.put(taken.position(), date);
                    days.add(ofIt);
                }
                Long weight = YearsAWayAllows.asLongOrNull(term.getValue());
                if (weight == null) {
                    return false;
                }
                parts.merge(new DatesThatHoldEveryStatement.Part(date, part,
                        taken.transformation().translation()), weight, Math::addExact);
            }
            Long constant = YearsAWayAllows.asLongOrNull(each.form().constant());
            if (constant == null) {
                return false;
            }
            asked.add(new DatesThatHoldEveryStatement.Statement(parts, constant, each.rel()));
        }
        return DatesThatHoldEveryStatement.some(asked, days) != null;
    }

    private void tieAll(Set<TermPath> places) {
        TermPath first = null;
        for (TermPath each : places) {
            above.putIfAbsent(each, each);
            if (first == null) {
                first = each;
            } else {
                tie(first, each);
            }
        }
    }

    private TermPath top(TermPath place) {
        TermPath at = place;
        while (!above.get(at).equals(at)) {
            at = above.get(at);
        }
        return at;
    }

    private void tie(TermPath one, TermPath other) {
        TermPath a = top(one);
        TermPath b = top(other);
        if (!a.equals(b)) {
            above.put(a, b);
        }
    }
}
