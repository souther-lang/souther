package souther.compiler.partition;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.TakenAs;

import java.math.BigInteger;
import java.time.LocalDate;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Dates at which statements of their parts all hold, found and then checked against the
 * calendar: the year, the month and the day of one date are three numbers a region holds apart,
 * and a statement weighing two of them may hold of numbers no date gives — the thirtieth of
 * February — or of some that one date does, February 2000.
 *
 * <p>The dates are what this answers, and not whether there are none. Where none is found nothing
 * is said: the search looks at a few of the years the statements leave, and turns away the ones
 * past what it looks through at all.
 *
 * <p>A date's parts are written as its year and, for each part, what that part comes to beside
 * the year. The second comes round with the calendar's cycle of four hundred years, so it is read
 * once over a cycle for each kind of year, and each statement is then a statement of the years of
 * the dates alone, which {@link YearsAWayAllows#holding} chooses. The dates are made of the years
 * chosen and checked part by part against every statement as written.
 */
final class DatesThatHoldEveryStatement {

    /** The dates a way may state the parts of for them to be looked for together. */
    static final int MOST_DATES = 2;

    /** How many choices of what the parts come to beside the years are looked through, over all
     *  the dates together. */
    static final int MOST_CHOICES = 4_096;

    /** A part of the date numbered {@code date}, taken after it is moved. */
    record Part(int date, TakenAs.DatePart which, DateTranslation moved) {}

    /** The weighed {@code parts} and {@code constant}, held against nought as {@code relation}. */
    record Statement(Map<Part, Long> parts, long constant, Rel relation) {}

    private DatesThatHoldEveryStatement() {
    }

    /**
     * Dates, one for each of {@code days}, at which every statement holds and every part of them
     * is taken of a day its move is defined at — or null where none is found.
     *
     * @param days the dates each date may be, as the days a move by nothing is defined at
     */
    static LocalDate[] some(List<Statement> statements, List<DateTranslation> days) {
        int dates = days.size();
        if (dates == 0 || dates > MOST_DATES) {
            return null;
        }
        List<List<Part>> partsOf = new ArrayList<>();
        List<DateTranslation> wherever = new ArrayList<>();
        for (int date = 0; date < dates; date++) {
            partsOf.add(new ArrayList<>());
            wherever.add(days.get(date));
        }
        for (Statement statement : statements) {
            for (Part part : statement.parts().keySet()) {
                if (part.date() < 0 || part.date() >= dates) {
                    return null;
                }
                if (!partsOf.get(part.date()).contains(part)) {
                    partsOf.get(part.date()).add(part);
                }
                DateTranslation every = wherever.get(part.date());
                wherever.set(part.date(), every == null ? null
                        : every.definedOnlyWhere(part.moved()));
            }
        }
        List<int[]> allowed = new ArrayList<>();
        List<Map<List<Long>, Kind>> kinds = new ArrayList<>();
        long choices = 1;
        for (int date = 0; date < dates; date++) {
            int[] years = wherever.get(date) == null ? null : wherever.get(date).wholeYears();
            if (years == null) {
                return null;
            }
            allowed.add(years);
            Map<List<Long>, Kind> ofIt = kindsOf(statements, partsOf.get(date));
            if (ofIt == null || ofIt.isEmpty()) {
                return null;
            }
            kinds.add(ofIt);
            choices *= ofIt.size();
            if (choices > MOST_CHOICES) {
                return null;
            }
        }
        return choose(statements, partsOf, kinds, allowed, wherever, new ArrayList<>());
    }

    /**
     * What the parts of a date come to beside its year, at the days of some years of a cycle:
     * {@code beside} is what the statements' parts of the date come to, the year left out, and
     * {@code years} the years of a cycle a day giving the parts that is.
     */
    private record Kind(BitSet years, Set<List<Integer>> beside) {}

    /**
     * The kinds of a date's days, by what the date's parts come to in each statement beside the
     * weighed year, or null where a sum is past what a whole number holds.
     */
    private static Map<List<Long>, Kind> kindsOf(List<Statement> statements, List<Part> parts) {
        List<PartsOfADateOverACycle.Moved> asked = parts.stream().map(part ->
                new PartsOfADateOverACycle.Moved(part.which(), part.moved().offsetDays()))
                .toList();
        Map<List<Long>, Kind> out = new LinkedHashMap<>();
        for (PartsOfADateOverACycle.Given each : PartsOfADateOverACycle.of(asked)) {
            List<Long> sums = new ArrayList<>(statements.size());
            for (Statement statement : statements) {
                long sum = 0;
                for (int at = 0; at < parts.size(); at++) {
                    Long weight = statement.parts().get(parts.get(at));
                    if (weight == null) {
                        continue;
                    }
                    try {
                        sum = Math.addExact(sum, Math.multiplyExact(weight,
                                (long) each.values().get(at)));
                    } catch (ArithmeticException _) {
                        return null;
                    }
                }
                sums.add(sum);
            }
            Kind kind = out.computeIfAbsent(List.copyOf(sums), _ -> new Kind(
                    new BitSet(PartsOfADateOverACycle.YEARS_OF_A_CYCLE), new LinkedHashSet<>()));
            kind.years().or(each.years());
            kind.beside().add(each.values());
        }
        return out;
    }

    /**
     * Dates for the kinds still to be chosen after {@code chosen}, taken in turn: at each choice
     * of a kind for every date, the years are chosen and the dates are made in them and checked.
     */
    private static LocalDate[] choose(List<Statement> statements, List<List<Part>> partsOf,
                                      List<Map<List<Long>, Kind>> kinds, List<int[]> allowed,
                                      List<DateTranslation> wherever,
                                      List<Map.Entry<List<Long>, Kind>> chosen) {
        if (chosen.size() < kinds.size()) {
            for (Map.Entry<List<Long>, Kind> kind : kinds.get(chosen.size()).entrySet()) {
                chosen.add(kind);
                LocalDate[] found = choose(statements, partsOf, kinds, allowed, wherever, chosen);
                chosen.removeLast();
                if (found != null) {
                    return found;
                }
            }
            return null;
        }
        List<YearsAWayAllows.Statement> ofTheYears = new ArrayList<>();
        for (int at = 0; at < statements.size(); at++) {
            Statement statement = statements.get(at);
            long constant = statement.constant();
            List<YearsAWayAllows.Year> years = new ArrayList<>();
            for (int date = 0; date < chosen.size(); date++) {
                try {
                    constant = Math.addExact(constant, chosen.get(date).getKey().get(at));
                } catch (ArithmeticException _) {
                    return null;
                }
                long weight = 0;
                for (Map.Entry<Part, Long> part : statement.parts().entrySet()) {
                    if (part.getKey().date() == date
                            && part.getKey().which() == TakenAs.DatePart.YEAR) {
                        try {
                            weight = Math.addExact(weight, part.getValue());
                        } catch (ArithmeticException _) {
                            return null;
                        }
                    }
                }
                if (weight != 0) {
                    years.add(new YearsAWayAllows.Year(date, ExactRatio.of(weight),
                            DateTranslation.none()));
                }
            }
            ofTheYears.add(new YearsAWayAllows.Statement(years, ExactRatio.of(constant),
                    statement.relation()));
        }
        List<BitSet> ofTheCycle = chosen.stream().map(kind -> kind.getValue().years()).toList();
        long[] years = YearsAWayAllows.holding(ofTheYears, ofTheCycle, allowed);
        if (years == null) {
            return null;
        }
        LocalDate[] dates = new LocalDate[chosen.size()];
        for (int date = 0; date < dates.length; date++) {
            dates[date] = aDayOf(partsOf.get(date), chosen.get(date).getValue(), years[date],
                    wherever.get(date));
            if (dates[date] == null) {
                return null;
            }
        }
        return everyStatementHoldsAt(statements, dates) ? dates : null;
    }

    /** A day of {@code year} every move is defined at whose parts come to one of {@code kind}'s
     *  beside the year, or null where there is none. */
    private static LocalDate aDayOf(List<Part> parts, Kind kind, long year,
                                   DateTranslation wherever) {
        LocalDate first = LocalDate.of((int) year, 1, 1);
        for (int at = 0; at < first.lengthOfYear(); at++) {
            long day = first.toEpochDay() + at;
            if (!wherever.definedAt(day)) {
                continue;
            }
            List<Integer> beside = new ArrayList<>(parts.size());
            for (Part part : parts) {
                LocalDate moved = LocalDate.ofEpochDay(day + part.moved().offsetDays());
                beside.add(part.which() == TakenAs.DatePart.YEAR
                        ? moved.getYear() - (int) year : part.which().of(moved));
            }
            if (kind.beside().contains(beside)) {
                return LocalDate.ofEpochDay(day);
            }
        }
        return null;
    }

    /**
     * Whether every statement holds at {@code dates}, each part taken of its date moved at a day
     * the move is defined at, and every term of it and its constant, their sizes added, inside
     * what a whole number holds: then no order the program adds them in passes it.
     */
    static boolean everyStatementHoldsAt(List<Statement> statements, LocalDate[] dates) {
        BigInteger greatest = BigInteger.valueOf(Long.MAX_VALUE);
        for (Statement statement : statements) {
            BigInteger sum = BigInteger.valueOf(statement.constant());
            BigInteger size = sum.abs();
            for (Map.Entry<Part, Long> each : statement.parts().entrySet()) {
                Part part = each.getKey();
                long origin = dates[part.date()].toEpochDay();
                if (!part.moved().definedAt(origin)) {
                    return false;
                }
                LocalDate moved = LocalDate.ofEpochDay(origin + part.moved().offsetDays());
                BigInteger term = BigInteger.valueOf(each.getValue())
                        .multiply(BigInteger.valueOf(part.which().of(moved)));
                sum = sum.add(term);
                size = size.add(term.abs());
            }
            if (size.compareTo(greatest) > 0 || !statement.relation().holds(sum.signum())) {
                return false;
            }
        }
        return true;
    }
}
