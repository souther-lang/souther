package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.TreeMap;

/**
 * Where each relation a statement of several holds together decides what the statement comes to.
 *
 * <p>A statement of several relations is one rule, and each relation in it is a line of that rule
 * only where crossing the line turns the statement round: {@code Int.max(a, b) <= g} is {@code a <=
 * g} and {@code b <= g} together, and moving {@code a} across {@code g} changes what the statement
 * comes to only where {@code b <= g} holds. That is the condition a line decides under, and it is
 * part of what the line means — a row against {@code a = g} where {@code b} is above {@code g} is a
 * row the statement answers the same way on both sides of the line.
 *
 * <p><b>Read off what the statement states, and not off how it is nested.</b> A relation decides
 * exactly where the statement with the relation holding and the statement with it failing come out
 * differently. Where a relation stands once, that is every part around it coming out the way that
 * leaves the outcome to it — the others of a conjunction holding, of a disjunction failing — and
 * where it stands twice it is not: {@code Decimal.max(0, gross - fee) <= g} states {@code gross -
 * fee >= 0} once held and once denied, and asked of each place it stands, one place would be read
 * with the other held still, which no row on the line can do.
 *
 * <p><b>Said as cases, each of them parts every one of which holds.</b> Where a line decides may be
 * one of several things: the line between the two arms of {@code Decimal.max} decides where the
 * difference is above {@code g} and {@code g} is below nought, or where neither is. Each case is a
 * set of parts a row can be composed to meet together, so a line looked for under each case is
 * looked for where it decides and nowhere else — and a line no case leaves a row at is one the
 * statement never turns on. None at all is a line that decides nowhere, whatever the row.
 *
 * <p><b>What this says is the relation turning alone, which is not yet a row crossing it.</b> The
 * parts are read as though each could come out either way with the others held still, and two of
 * them over the same number cannot: {@code Int.min(a, 11 - a) > 5} decides on {@code 11 - a > 5}
 * where {@code a > 5}, and every row that crosses that line from six to five takes {@code a > 5}
 * across with it. So a case is where the line decides only where rows on both sides of the line
 * can be in it, which is asked of the rows and not here.
 */
public final class WhereEachLineDecides {

    /**
     * How many distinct parts a statement can have and still be read part against part.
     *
     * <p>Every way the parts can come out is asked, which doubles with each part. Past this, where a
     * line decides is said as one case: the statement with the line held against the statement with
     * it failing, which is the same condition with nothing taken apart for a reader to compose
     * against.
     */
    private static final int MOST_PARTS_READ_TOGETHER = 12;

    /**
     * How many places parts stand at, over every way the parts can come out, the statement is read
     * at before it is said as one case instead.
     *
     * <p>The work of reading it part against part is every way times every place a part stands, and
     * a statement can be long over few parts as readily as short over many. Bounded by the parts
     * alone, a statement written out over a dozen of them took as long to read as a module.
     */
    private static final long MOST_PLACES_READ = 1L << 17;

    /** How many cases where a line decides is said in before it is said as one. */
    static final int MOST_CASES = 16;

    private WhereEachLineDecides() {
    }

    /**
     * One relation of the statement and where it decides.
     *
     * @param line  the relation, held: which way round it was written is the statement's and not
     *              the line's
     * @param cases where it decides, as cases any one of which is enough: each a part, a conjunction
     *              of parts, or nothing asked at all. Empty where it decides nowhere. None of them
     *              names {@code line}
     */
    public record Decides(Proposition.Compared line, List<Proposition> cases) {

        public Decides {
            Objects.requireNonNull(line, "a line is some relation");
            cases = List.copyOf(cases);
            if (!line.holds()) {
                throw new IllegalArgumentException("a line is the relation held: " + line);
            }
        }
    }

    /**
     * Every relation {@code stated} holds together, once each and in the order of their spellings,
     * with where each decides.
     *
     * <p>Only the relations that a conjunction or a disjunction joins. What a quantifier says of
     * each element, and what a closure says on each application, are one part each here: a relation
     * inside one is about an element or an application and not about the row.
     */
    public static List<Decides> in(Proposition stated) {
        Map<String, Proposition> parts = new TreeMap<>();
        Map<String, Literal> leaves = new TreeMap<>();
        gather(stated, parts, leaves);
        List<Proposition> named = List.copyOf(parts.values());
        Map<String, Integer> index = new TreeMap<>();
        for (int i = 0; i < named.size(); i++) {
            index.put(named.get(i).key(), i);
        }
        boolean[] table = named.size() <= MOST_PARTS_READ_TOGETHER
                && (1L << named.size()) * placesIn(stated) <= MOST_PLACES_READ
                ? tabulated(stated, leaves, index, named.size()) : null;
        List<Decides> out = new ArrayList<>();
        for (int at = 0; at < named.size(); at++) {
            if (!(named.get(at) instanceof Proposition.Compared line)) {
                continue;
            }
            List<Proposition> cases = table == null ? null : casesOf(table, at, named);
            out.add(new Decides(line, cases != null ? cases
                    : List.of(heldAgainstItsDenial(stated, line))));
        }
        return List.copyOf(out);
    }

    /**
     * A part as it stands in the statement: which part it is, by the spelling of it held, and
     * whether it stands held or denied.
     */
    private record Literal(String part, boolean held) {}

    /** Every part {@code stated} joins, held, and each place one stands, by its own spelling. */
    private static void gather(Proposition stated, Map<String, Proposition> parts,
                               Map<String, Literal> leaves) {
        switch (stated) {
            case Proposition.All all -> all.parts().forEach(part -> gather(part, parts, leaves));
            case Proposition.Any any -> any.parts().forEach(part -> gather(part, parts, leaves));
            default -> {
                Proposition held = held(stated);
                parts.putIfAbsent(held.key(), held);
                leaves.putIfAbsent(stated.key(), new Literal(held.key(), held == stated));
            }
        }
    }

    /**
     * {@code part} held, where it says which way round it stands; itself where it does not, which a
     * closure read on its applications and a statement settled for every row do not.
     */
    private static Proposition held(Proposition part) {
        boolean holds = switch (part) {
            case Proposition.Compared compared -> compared.holds();
            case Proposition.Truth truth -> truth.holds();
            case Proposition.InCases cases -> cases.holds();
            case Proposition.Present present -> present.holds();
            case Proposition.SameValue same -> same.holds();
            case Proposition.Unread unread -> unread.holds();
            case Proposition.Some some -> some.holds();
            case Proposition.OnAnApplication _, Proposition.Always _ -> true;
            case Proposition.All _, Proposition.Any _ -> throw new IllegalArgumentException(
                    "a part is what a conjunction or a disjunction joins: " + part);
        };
        return holds ? part : part.denied();
    }

    /** How many places a part stands at in {@code stated}, each counted every time it stands. */
    private static long placesIn(Proposition stated) {
        return switch (stated) {
            case Proposition.All all ->
                    all.parts().stream().mapToLong(WhereEachLineDecides::placesIn).sum();
            case Proposition.Any any ->
                    any.parts().stream().mapToLong(WhereEachLineDecides::placesIn).sum();
            default -> 1;
        };
    }

    /** What {@code stated} comes to for every way its {@code count} parts can come out, the
     *  {@code i}th part held where bit {@code i} is set. */
    private static boolean[] tabulated(Proposition stated, Map<String, Literal> leaves,
                                       Map<String, Integer> index, int count) {
        boolean[] table = new boolean[1 << count];
        for (int ways = 0; ways < table.length; ways++) {
            table[ways] = holds(stated, leaves, index, ways);
        }
        return table;
    }

    private static boolean holds(Proposition stated, Map<String, Literal> leaves,
                                 Map<String, Integer> index, int ways) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream()
                    .allMatch(part -> holds(part, leaves, index, ways));
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(part -> holds(part, leaves, index, ways));
            default -> {
                Literal leaf = leaves.get(stated.key());
                yield (((ways >> index.get(leaf.part())) & 1) == 1) == leaf.held();
            }
        };
    }

    /**
     * Where the {@code at}th part decides, read off what the statement comes to every way its parts
     * can come out, as cases — or null where there are more of them than {@link #MOST_CASES}.
     *
     * <p>The line decides at a way its other parts come out where the statement comes out
     * differently with the line held and with it failing. The cases are taken by asking the other
     * parts one at a time, in order, each only where what is left still turns on it: a part every
     * way left decides under, or none does, says nothing more.
     */
    private static List<Proposition> casesOf(boolean[] table, int at, List<Proposition> named) {
        int line = 1 << at;
        boolean[] decides = new boolean[table.length];
        for (int ways = 0; ways < table.length; ways++) {
            decides[ways] = (ways & line) == 0 && table[ways] != table[ways | line];
        }
        List<List<Proposition>> cases = new ArrayList<>();
        if (!split(decides, line, 0, 0, new ArrayList<>(), named, at, cases)) {
            return null;
        }
        return cases.stream().map(Proposition::all).toList();
    }

    /**
     * The cases under {@code asked}, the parts whose bits are {@code fixed} coming out as
     * {@code values} says — or false as soon as there are more than {@link #MOST_CASES}, so the
     * limit bounds the work and not only what is kept.
     */
    private static boolean split(boolean[] decides, int line, int fixed, int values,
                                 List<Proposition> asked, List<Proposition> named, int at,
                                 List<List<Proposition>> into) {
        boolean some = false;
        boolean every = true;
        for (int ways = 0; ways < decides.length; ways++) {
            if ((ways & line) == 0 && (ways & fixed) == values) {
                some |= decides[ways];
                every &= decides[ways];
            }
        }
        if (!some) {
            return true;
        }
        if (every) {
            into.add(List.copyOf(asked));
            return into.size() <= MOST_CASES;
        }
        for (int part = 0; part < named.size(); part++) {
            int its = 1 << part;
            if (part == at || (fixed & its) != 0 || !turnsOn(decides, line, fixed, values, its)) {
                continue;
            }
            List<Proposition> held = new ArrayList<>(asked);
            held.add(named.get(part));
            if (!split(decides, line, fixed | its, values | its, held, named, at, into)) {
                return false;
            }
            List<Proposition> failing = new ArrayList<>(asked);
            failing.add(named.get(part).denied());
            return split(decides, line, fixed | its, values, failing, named, at, into);
        }
        throw new IllegalStateException("where a line decides turns on some part where it is"
                + " neither everywhere nor nowhere");
    }

    /** Whether, the parts at {@code fixed} coming out as {@code values}, where the line decides
     *  turns on the part at {@code its}. */
    private static boolean turnsOn(boolean[] decides, int line, int fixed, int values, int its) {
        for (int ways = 0; ways < decides.length; ways++) {
            if ((ways & line) == 0 && (ways & its) == 0 && (ways & fixed) == values
                    && decides[ways] != decides[ways | its]) {
                return true;
            }
        }
        return false;
    }

    /**
     * Where {@code line} decides, said as the statement with it held against the statement with it
     * failing: one of them holding and the other not.
     */
    private static Proposition heldAgainstItsDenial(Proposition stated,
                                                    Proposition.Compared line) {
        Proposition held = with(stated, line, true);
        Proposition failing = with(stated, line, false);
        return Proposition.any(List.of(
                Proposition.all(List.of(held, failing.denied())),
                Proposition.all(List.of(held.denied(), failing))));
    }

    /** {@code stated} with every place {@code line} stands come out {@code holds}. */
    private static Proposition with(Proposition stated, Proposition.Compared line,
                                    boolean holds) {
        return switch (stated) {
            case Proposition.All all -> Proposition.all(all.parts().stream()
                    .map(part -> with(part, line, holds)).toList());
            case Proposition.Any any -> Proposition.any(any.parts().stream()
                    .map(part -> with(part, line, holds)).toList());
            case Proposition.Compared compared when compared.relation().equals(line.relation()) ->
                    new Proposition.Always(compared.holds() == holds);
            default -> stated;
        };
    }
}
