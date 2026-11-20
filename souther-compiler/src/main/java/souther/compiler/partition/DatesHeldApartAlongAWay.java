package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * What a way says of the places it names, as the sets of places it ties together, and which of
 * those sets some values hold everything the way says of: a fact of the way, asked once for it and
 * read by each side shown along it.
 *
 * <p>Two places are tied where one statement or one narrowing of the way reads both, where one is
 * at or under the other, or through a place tied to each. What a statement reads is every place
 * it turns on, and what each of its numbers is read off ({@link NumericTerm#placesReadOff}): a
 * product reads every place of either factor, and a number taken with arguments the places of
 * those too, so no number is read as fewer places than it turns on. The sets are worked out when
 * first asked of, which asks every two places whether one bears on the other, and kept for every
 * question after.
 *
 * <p>A set is held where every statement and narrowing reading a place of it is either a form of
 * parts of dates or a truth of a place, and some values hold them all. The forms are asked of the
 * calendar ({@link DatesThatHoldEveryStatement}), as statements of one date each, which a part of
 * a date inside a container is not ({@link WhatStatementsOfOneFormDecide#outsideEveryContainer}),
 * and over dates the declarations leave every date, or every date between its ends. A truth holds
 * at a place a row may hold either truth at, and each place is held to one of them: a place of a
 * truth is no number of a form, so the truths and the forms are held apart.
 *
 * <p>A set anything else reads is not held: nothing asked it. It is still said to be held by no
 * dates where no dates hold its forms. A form of anything but parts of dates is not asked of the
 * calendar, and the set is neither held nor said to be held by no dates.
 */
final class DatesHeldApartAlongAWay {

    private final List<UndividedByARelation.OnAWay> conditions;
    private final List<TakenConstraint> narrowing;
    private final Collection<TermPath> alsoNamed;
    private final Function<NumericTerm.TakenOf, DateTranslation> daysOf;
    private final Predicate<TermPath> eitherTruthAt;
    /** The sets, once worked out. */
    private Sets sets;
    /** What is answered of each set, by the place it is filed under, once asked. */
    private final Map<TermPath, DatesThatHoldEveryStatement.Answer> held = new LinkedHashMap<>();

    private DatesHeldApartAlongAWay(List<UndividedByARelation.OnAWay> conditions,
                                    List<TakenConstraint> narrowing,
                                    Collection<TermPath> alsoNamed,
                                    Function<NumericTerm.TakenOf, DateTranslation> daysOf,
                                    Predicate<TermPath> eitherTruthAt) {
        this.conditions = conditions;
        this.narrowing = narrowing;
        this.alsoNamed = alsoNamed;
        this.daysOf = daysOf;
        this.eitherTruthAt = eitherTruthAt;
    }

    /**
     * The sets of places {@code conditions} and {@code narrowing} tie, among them the places
     * {@code alsoNamed} are read off, which nothing need state.
     *
     * @param daysOf        the dates the declarations leave the date a part is taken of, as the
     *                      days a move by nothing is defined at, or null where they leave it
     *                      anything else
     * @param eitherTruthAt whether a row may hold either truth at a place, whatever else it holds
     */
    static DatesHeldApartAlongAWay of(List<UndividedByARelation.OnAWay> conditions,
                                      List<TakenConstraint> narrowing,
                                      Collection<TermPath> alsoNamed,
                                      Function<NumericTerm.TakenOf, DateTranslation> daysOf,
                                      Predicate<TermPath> eitherTruthAt) {
        return new DatesHeldApartAlongAWay(conditions, narrowing, alsoNamed, daysOf,
                eitherTruthAt);
    }

    /** Every place {@code terms} are read off, in order, each once. */
    static Set<TermPath> placesReadOff(Collection<NumericTerm> terms) {
        Set<TermPath> out = new LinkedHashSet<>();
        terms.forEach(term -> out.addAll(term.placesReadOff()));
        return out;
    }

    /**
     * Every place {@code statement} turns on, as it says ({@link UndividedByARelation.OnAWay#turnsOn}
     * — the places a statement the run says whether it held reads, beside the positions), and
     * every place a number it relates is read off. Where it does not say, its positions.
     */
    private static Set<TermPath> placesOf(UndividedByARelation.OnAWay statement) {
        Set<TermPath> out = new LinkedHashSet<>(
                statement.turnsOn().orElse(statement.positions()));
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
        Sets of = sets();
        if (!of.names(place)) {
            return Optional.empty();
        }
        for (TermPath ofTheSide : side.placesReadOff()) {
            if (!of.names(ofTheSide) || of.top(ofTheSide).equals(of.top(place))) {
                return Optional.empty();
            }
        }
        return answerOf(of.top(place)) instanceof DatesThatHoldEveryStatement.Found
                ? Optional.of(tiedTo(place)) : Optional.empty();
    }

    /**
     * Whether no dates hold every statement and narrowing this was made of that reads some set:
     * then no row holds them all. A set no dates hold is read by parts of dates and nothing else,
     * so where nothing this was made of reads one, none is, and no set is worked out.
     */
    boolean someSetNoDatesHold() {
        if (conditions.stream().noneMatch(each -> each.affine() != null
                && readsAPartOfADate(each.affine().terms()))
                && narrowing.stream().noneMatch(each -> readsAPartOfADate(each.terms()))) {
            return false;
        }
        for (TermPath each : sets().stated.keySet()) {
            if (answerOf(each) == DatesThatHoldEveryStatement.Otherwise.NONE_HOLD) {
                return true;
            }
        }
        return false;
    }

    private static boolean readsAPartOfADate(Collection<NumericTerm> terms) {
        return terms.stream().anyMatch(term -> term instanceof NumericTerm.TakenOf taken
                && taken.takenAs() instanceof TakenAs.PartOfDate);
    }

    private DatesThatHoldEveryStatement.Answer answerOf(TermPath filed) {
        return held.computeIfAbsent(filed, this::someDatesHold);
    }

    /** The places the way ties to {@code place}, itself among them; none where the way was not
     *  told of it. */
    Set<TermPath> tiedTo(TermPath place) {
        Sets of = sets();
        Set<TermPath> out = new LinkedHashSet<>();
        if (of.names(place)) {
            TermPath filed = of.top(place);
            for (TermPath each : of.above.keySet()) {
                if (of.top(each).equals(filed)) {
                    out.add(each);
                }
            }
        }
        return out;
    }

    /**
     * What is answered of every statement and narrowing of the way reading the set filed under
     * {@code filed}: the calendar's answer of its forms, no dates where it states none, and
     * nothing found where a truth of it is not held or something else reads it. Dates holding the
     * forms are not shown to hold the rest, and where no dates hold the forms none hold the rest
     * beside them.
     */
    private DatesThatHoldEveryStatement.Answer someDatesHold(TermPath filed) {
        Sets of = sets();
        List<TakenConstraint.Affine> forms = of.stated.getOrDefault(filed, List.of());
        DatesThatHoldEveryStatement.Answer ofTheForms = forms.isEmpty()
                ? new DatesThatHoldEveryStatement.Found(List.of()) : someDatesHoldAll(forms);
        boolean allHeld = !of.readByNoForm.contains(filed)
                && of.truths.getOrDefault(filed, Map.of()).entrySet().stream().allMatch(each ->
                        each.getValue().size() == 1 && eitherTruthAt.test(each.getKey()));
        return !allHeld && ofTheForms instanceof DatesThatHoldEveryStatement.Found
                ? DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN : ofTheForms;
    }

    /**
     * What the calendar answers of {@code statements}: not shown where one reads inside a
     * container, a term of one is anything but a part of a date the declarations leave every
     * date, or every date between its ends, or a weight or a constant is not a whole number.
     */
    private DatesThatHoldEveryStatement.Answer someDatesHoldAll(
            List<TakenConstraint.Affine> statements) {
        DatesThatHoldEveryStatement.Answer notShown =
                DatesThatHoldEveryStatement.Otherwise.NOT_SHOWN;
        Map<TermPath, Integer> dates = new LinkedHashMap<>();
        List<DateTranslation> days = new ArrayList<>();
        List<DatesThatHoldEveryStatement.Statement> asked = new ArrayList<>();
        for (TakenConstraint.Affine each : statements) {
            if (!WhatStatementsOfOneFormDecide.outsideEveryContainer(each)) {
                return notShown;
            }
            // Two terms may be one part of one date, and their weights are that part's together.
            Map<DatesThatHoldEveryStatement.Part, BigInteger> weighed = new LinkedHashMap<>();
            for (Map.Entry<NumericTerm, ExactRatio> term : each.form().coefs().entrySet()) {
                if (!(term.getKey() instanceof NumericTerm.TakenOf taken)
                        || !(taken.takenAs() instanceof TakenAs.PartOfDate(
                                TakenAs.DatePart part))) {
                    return notShown;
                }
                Integer date = dates.get(taken.position());
                if (date == null) {
                    DateTranslation ofIt = daysOf.apply(taken);
                    if (ofIt == null) {
                        return notShown;
                    }
                    date = dates.size();
                    dates.put(taken.position(), date);
                    days.add(ofIt);
                }
                Long weight = YearsAWayAllows.asLongOrNull(term.getValue());
                if (weight == null) {
                    return notShown;
                }
                weighed.merge(new DatesThatHoldEveryStatement.Part(date, part,
                        taken.transformation().translation()), BigInteger.valueOf(weight),
                        BigInteger::add);
            }
            Map<DatesThatHoldEveryStatement.Part, Long> parts = new LinkedHashMap<>();
            for (Map.Entry<DatesThatHoldEveryStatement.Part, BigInteger> part
                    : weighed.entrySet()) {
                if (part.getValue().bitLength() >= Long.SIZE) {
                    return notShown;
                }
                parts.put(part.getKey(), part.getValue().longValue());
            }
            Long constant = YearsAWayAllows.asLongOrNull(each.form().constant());
            if (constant == null) {
                return notShown;
            }
            asked.add(new DatesThatHoldEveryStatement.Statement(parts, constant, each.rel()));
        }
        return DatesThatHoldEveryStatement.some(asked, days);
    }

    private Sets sets() {
        if (sets == null) {
            sets = Sets.of(conditions, narrowing, alsoNamed);
        }
        return sets;
    }

    /**
     * The sets of places a way ties, each filed under one of its places, and the forms of the
     * statements and narrowings reading each set, filed the same way: every place one of them
     * reads is tied to the others it reads, so each is of one set. A set some statement or
     * narrowing that is no form reads is filed among {@link #readByNoForm}, unless it is a truth,
     * which is filed among {@link #truths} by its place.
     */
    private static final class Sets {

        private final Map<TermPath, TermPath> above = new LinkedHashMap<>();
        private final Map<TermPath, List<TakenConstraint.Affine>> stated = new LinkedHashMap<>();
        private final Set<TermPath> readByNoForm = new LinkedHashSet<>();
        /** The truths each set's places are held to, by the place. */
        private final Map<TermPath, Map<TermPath, Set<Boolean>>> truths = new LinkedHashMap<>();

        static Sets of(List<UndividedByARelation.OnAWay> conditions,
                       List<TakenConstraint> narrowing, Collection<TermPath> alsoNamed) {
            Sets out = new Sets();
            alsoNamed.forEach(place -> out.above.putIfAbsent(place, place));
            List<Set<TermPath>> read = new ArrayList<>();
            List<TakenConstraint.Affine> what = new ArrayList<>();
            List<RowDemand.ATruth> truthOf = new ArrayList<>();
            for (UndividedByARelation.OnAWay each : conditions) {
                read.add(placesOf(each));
                what.add(each.affine());
                truthOf.add(each.truth());
            }
            for (TakenConstraint each : narrowing) {
                read.add(placesReadOff(each.terms()));
                what.add(each instanceof TakenConstraint.Affine affine ? affine : null);
                truthOf.add(null);
            }
            read.forEach(out::tieAll);
            List<TermPath> places = List.copyOf(out.above.keySet());
            for (TermPath one : places) {
                for (TermPath other : places) {
                    if (!one.equals(other) && (one.bearsOn(other) || other.bearsOn(one))) {
                        out.tie(one, other);
                    }
                }
            }
            for (int at = 0; at < read.size(); at++) {
                if (read.get(at).isEmpty()) {
                    continue;
                }
                TermPath filed = out.top(read.get(at).iterator().next());
                RowDemand.ATruth truth = truthOf.get(at);
                if (truth != null) {
                    out.truths.computeIfAbsent(filed, _ -> new LinkedHashMap<>())
                            .computeIfAbsent(truth.at(), _ -> new LinkedHashSet<>())
                            .add(truth.held());
                } else if (what.get(at) == null) {
                    out.readByNoForm.add(filed);
                } else {
                    out.stated.computeIfAbsent(filed, _ -> new ArrayList<>()).add(what.get(at));
                }
            }
            return out;
        }

        boolean names(TermPath place) {
            return above.containsKey(place);
        }

        TermPath top(TermPath place) {
            TermPath at = place;
            while (!above.get(at).equals(at)) {
                at = above.get(at);
            }
            return at;
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

        private void tie(TermPath one, TermPath other) {
            TermPath a = top(one);
            TermPath b = top(other);
            if (!a.equals(b)) {
                above.put(a, b);
            }
        }
    }
}
