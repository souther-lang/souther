package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
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
 * <p><b>And which way round it turns there.</b> A line is a relation held, and the statement may
 * hold on the side where it fails: {@code month.value <= minimum(term)} holds its line as {@code
 * month.value > 12} where {@code term} is {@code OneYear}, and the statement holds below that line.
 * So each case says which side of the line the statement holds on, and a case is one side or the
 * other and never both: a part that leaves the statement holding with the line at some of its ways
 * and against it at others is a part the cases are told apart by.
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

    /** How many cases where a line decides is said in before it is said as one on each side of
     *  it. */
    static final int MOST_CASES = 16;

    private WhereEachLineDecides() {
    }

    /**
     * One relation of the statement and where it decides.
     *
     * @param line  the relation, held: which way round it was written is the statement's and not
     *              the line's
     * @param cases where it decides, as cases any one of which is enough, each with the side of
     *              the line the statement holds on there. Empty where it decides nowhere
     */
    public record Decides(Proposition.Compared line, List<Case> cases) {

        public Decides {
            Objects.requireNonNull(line, "a line is some relation");
            cases = List.copyOf(cases);
            if (!line.holds()) {
                throw new IllegalArgumentException("a line is the relation held: " + line);
            }
        }
    }

    /**
     * One case of where a line decides, and the side of the line the statement holds on there.
     *
     * @param where            what holds beside the line in this case: a part, a conjunction of
     *                         parts, or nothing asked at all. It never names the line
     * @param holdsWithTheLine whether the statement holds here on the side where the line holds;
     *                         false where it holds on the side where the line fails
     */
    public record Case(Proposition where, boolean holdsWithTheLine) {

        public Case {
            Objects.requireNonNull(where, "a case of where a line decides is somewhere");
        }

        /** A line that decides wherever a row is, the statement holding where it does. */
        public static Case everywhere() {
            return new Case(new Proposition.Always(true), true);
        }
    }

    /**
     * Every relation {@code stated} holds together, once each and in the order of their spellings,
     * with where each decides.
     *
     * <p>Only the relations that a conjunction or a disjunction joins, and the ones a quantifier
     * says of the element it chose. What a closure says on each application is one part here.
     *
     * <p>A relation inside a quantifier is a line where the row's element the quantifier chose
     * crosses it, and it decides where two things hold at once: the quantifier coming out one way
     * or the other turns the statement, and the relation turns what the quantifier says of that
     * element ({@link #read}). Each is asked of what it stands in, with every other quantifier one
     * part there. Two quantifiers over one container are about two elements, which may be
     * different ones; read as one statement about one element, what each asks would be asked of
     * that one, and two things no element is at once but two elements are would read as a
     * statement no row turns. So a relation that stands inside several quantifiers is a line in
     * each of them, and decides wherever it decides in any.
     */
    public static List<Decides> in(Proposition writtenAs) {
        Map<String, Proposition.Compared> lines = new TreeMap<>();
        Map<String, List<List<List<Case>>>> standings = new TreeMap<>();
        read(writtenAs, writtenAs, null, List.of(), lines, standings);
        List<Decides> out = new ArrayList<>();
        lines.forEach((key, line) -> out.add(new Decides(line,
                whereItStands(line, casesOf(standings.get(key))))));
        return List.copyOf(out);
    }

    /**
     * {@code cases}, each said of a value that is the case {@code line}'s positions are written
     * under: a line at a field of one case of a value decides where the value is that case.
     *
     * <p>Nothing reading the parts of a case knows that one value is one case, so a case can ask
     * of the value what only another case of it holds — a field of that other case at some number,
     * or the value being that other case. Asked of the value the line is at, the first is about a
     * field the value does not have, and is no part of where the line decides; the second asks the
     * value to be two cases, and is no place the line is. So the one is left out and the other
     * case with it, and every case is said with the case the line is at.
     */
    private static List<Case> whereItStands(Proposition.Compared line, List<Case> cases) {
        Map<TermPath, CasesLeft> at = casesItIsOver(line);
        if (at.isEmpty()) {
            return cases;
        }
        List<Proposition> stands = new ArrayList<>();
        at.forEach((position, narrowed) -> {
            Proposition standing = standing(position, narrowed);
            if (standing != null) {
                stands.add(standing);
            }
        });
        List<Case> out = new ArrayList<>();
        cases:
        for (Case each : cases) {
            List<Proposition> parts = new ArrayList<>();
            for (Proposition part : each.where() instanceof Proposition.All all ? all.parts()
                    : List.of(each.where())) {
                switch (asked(part, at)) {
                    case OF_ANOTHER_CASE -> { }
                    case NOT_THERE -> {
                        continue cases;
                    }
                    case THERE -> parts.add(part);
                }
            }
            parts.addAll(stands);
            out.add(new Case(Proposition.all(parts), each.holdsWithTheLine()));
        }
        return out;
    }

    /**
     * That the value at {@code position} is {@code narrowed}, in the words a row is asked it in:
     * one of some cases of a sum, or holding a value or none — or null where it is neither, which
     * leaves the case unsaid and the line no narrower.
     */
    private static Proposition standing(TermPath position, CasesLeft narrowed) {
        DecisionSubject.AnInput value = new DecisionSubject.AnInput(position);
        List<Refinement> atoms = narrowed.atoms();
        if (atoms.stream().allMatch(Refinement.SumCase.class::isInstance)) {
            return new Proposition.InCases(value, narrowed, true);
        }
        if (atoms.size() == 1 && atoms.getFirst() instanceof Refinement.Presence presence) {
            return new Proposition.Present(value, presence.present());
        }
        return null;
    }

    /** What a part of a case comes to, asked of the value a line stands at. */
    private enum AskedOfTheValue {
        /** Something of the value as it is, which the case asks. */
        THERE,
        /** Something only another case of it has, which the value does not. */
        OF_ANOTHER_CASE,
        /** That the value is a case it is not, which leaves the line nowhere. */
        NOT_THERE
    }

    /** What {@code part} comes to of a value that is the cases {@code at} says, position by
     *  position. */
    private static AskedOfTheValue asked(Proposition part, Map<TermPath, CasesLeft> at) {
        if (part instanceof Proposition.InCases(DecisionSubject.AnInput(TermPath of),
                CasesLeft cases, boolean holds, var _) && at.containsKey(of)) {
            CasesLeft stands = at.get(of);
            boolean meets = stands.meet(cases) != null;
            if ((holds && !meets) || (!holds && stands.within(cases))) {
                return AskedOfTheValue.NOT_THERE;
            }
            return holds ? AskedOfTheValue.THERE : AskedOfTheValue.OF_ANOTHER_CASE;
        }
        // Whether an optional holds a value, asked of one the line stands under holding one or
        // none.
        if (part instanceof Proposition.Present(DecisionSubject.AnInput(TermPath of),
                boolean holds, var _) && at.containsKey(of)
                && at.get(of).atoms().size() == 1
                && at.get(of).atoms().getFirst() instanceof Refinement.Presence presence) {
            return presence.present() == holds ? AskedOfTheValue.THERE : AskedOfTheValue.NOT_THERE;
        }
        for (TermPath position : positionsOf(part)) {
            List<TermPath.Step> steps = position.steps();
            for (int step = 0; step < steps.size(); step++) {
                CasesLeft stands = at.get(new TermPath(position.head(), steps.subList(0, step)));
                if (stands != null && steps.get(step) instanceof TermPath.Step.Refine(
                        CasesLeft cases) && stands.meet(cases) == null) {
                    return AskedOfTheValue.OF_ANOTHER_CASE;
                }
            }
        }
        return AskedOfTheValue.THERE;
    }

    /** The positions of the input a part of a case is about, where it is one thing of one value;
     *  none for a part that is more than that. */
    private static List<TermPath> positionsOf(Proposition part) {
        List<TermPath> out = new ArrayList<>();
        switch (part) {
            case Proposition.Compared compared -> {
                switch (compared.relation()) {
                    case Relation.Affine affine -> affine.form().coefs().keySet()
                            .forEach(quantity -> {
                                if (quantity instanceof DecisionAtom.OfTheInput(var term)) {
                                    out.add(term.subjectPath());
                                }
                            });
                    case Relation.Ordered ordered -> {
                        if (ordered.term() instanceof DecisionAtom.OfTheInput(var term)) {
                            out.add(term.subjectPath());
                        }
                    }
                }
            }
            case Proposition.Truth(DecisionSubject.AnInput(TermPath of), var _, var _) ->
                    out.add(of);
            case Proposition.InCases(DecisionSubject.AnInput(TermPath of), var _, var _, var _) ->
                    out.add(of);
            case Proposition.Present(DecisionSubject.AnInput(TermPath of), var _, var _) ->
                    out.add(of);
            default -> { }
        }
        return out;
    }

    /** Each position a position {@code line} is over narrows, with the cases it narrows it to. */
    private static Map<TermPath, CasesLeft> casesItIsOver(Proposition.Compared line) {
        Map<TermPath, CasesLeft> out = new LinkedHashMap<>();
        for (TermPath position : positionsOf(line)) {
            List<TermPath.Step> steps = position.steps();
            for (int at = 0; at < steps.size(); at++) {
                if (steps.get(at) instanceof TermPath.Step.Refine(CasesLeft cases)) {
                    out.merge(new TermPath(position.head(), steps.subList(0, at)), cases,
                            (one, other) -> one.meet(other) == null ? one : one.meet(other));
                }
            }
        }
        return out;
    }

    /**
     * Adds every relation {@code stated} joins to {@code lines}, and the relations inside each
     * quantifier it joins held that says a relation of the element it chose, each with how it
     * stands: where each thing around it turns what holds it, outermost first, and where it turns
     * what it stands in.
     *
     * <p>A relation inside a quantifier and not about the element it chose is about the row, and
     * stands wherever it is written — so it is asked of the statement whole, every quantifier it
     * stands in moved with it.
     *
     * @param whole   the statement as written
     * @param element the container whose element {@code stated} is said of, or null where
     *                {@code stated} is the statement itself
     * @param around  where each quantifier {@code stated} is inside turns what holds it
     */
    private static void read(Proposition stated, Proposition whole, DecisionSubject element,
                             List<List<Case>> around,
                             Map<String, Proposition.Compared> lines,
                             Map<String, List<List<List<Case>>>> standings) {
        Reading reading = Reading.of(stated);
        for (Proposition part : reading.named()) {
            if (part instanceof Proposition.Compared line) {
                List<List<Case>> factors = new ArrayList<>(around);
                if (element == null || line.mayTurnOnAnElementOf(element)) {
                    factors.add(reading.turnsOn(line));
                } else {
                    factors = List.of(heldAgainstItsDenial(whole, line));
                }
                lines.putIfAbsent(line.key(), line);
                standings.computeIfAbsent(line.key(), k -> new ArrayList<>()).add(factors);
            } else if (part instanceof Proposition.Some some && reading.standsHeld(some)
                    && statesARelation(some.ofTheElement())) {
                List<List<Case>> inside = new ArrayList<>(around);
                inside.add(reading.turnsOn(some));
                read(some.ofTheElement(), whole, some.container(), inside, lines, standings);
            }
        }
    }

    /**
     * One statement read part against part: the parts it joins, each place one stands, and what
     * it comes to every way they can come out — or no table where that is more than is read.
     */
    private static final class Reading {

        private final Proposition stated;
        private final List<Proposition> named;
        private final Map<String, Integer> index;
        private final Map<String, Literal> leaves;
        private final boolean[] table;
        private final boolean[] possible;

        private Reading(Proposition stated, List<Proposition> named, Map<String, Integer> index,
                        Map<String, Literal> leaves, boolean[] table, boolean[] possible) {
            this.stated = stated;
            this.named = named;
            this.index = index;
            this.leaves = leaves;
            this.table = table;
            this.possible = possible;
        }

        /** The parts the statement joins, held, in the order of their spellings. */
        List<Proposition> named() {
            return named;
        }

        static Reading of(Proposition stated) {
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
            return new Reading(stated, named, index, leaves, table,
                    table == null ? null : possible(named));
        }

        /**
         * Where {@code part} turns the statement, as cases.
         *
         * <p>The table holds each part as one thing that comes out one way, which a part standing
         * as well inside a quantifier it is not about is not: there it is the same thing of the
         * same row, and comes out the way the part does. Said as one case on each side then, which
         * moves it everywhere it stands.
         */
        List<Case> turnsOn(Proposition part) {
            if (insideAWholeQuantifier(stated, part)) {
                return heldAgainstItsDenial(stated, part);
            }
            List<Case> cases = table != null ? casesOf(table, possible, index.get(part.key()), named)
                    : inEachCaseOfAValue(stated, named, part);
            return cases != null ? cases : heldAgainstItsDenial(stated, part);
        }

        /** Whether {@code quantifier} stands held somewhere in the statement. */
        boolean standsHeld(Proposition.Some quantifier) {
            return leaves.values().stream().anyMatch(leaf ->
                    leaf.held() && leaf.part().equals(quantifier.key()));
        }
    }

    /**
     * Where a line decides, off each way it stands: a case of what each thing around it is turned
     * under, taken together — or, where those are more than {@link #MOST_CASES}, said as one case
     * on each side of the line.
     */
    private static List<Case> casesOf(List<List<List<Case>>> standings) {
        List<Case> cases = new ArrayList<>();
        for (List<List<Case>> factors : standings) {
            List<Case> here = takenTogether(factors);
            if (here == null) {
                cases = null;
                break;
            }
            cases.addAll(here);
        }
        List<Case> each = cases == null ? null : cases.stream().distinct().toList();
        if (each != null && each.size() <= MOST_CASES) {
            return each;
        }
        // Each thing the line stands inside said as one case on each side, so the ways of taking
        // them together are two for each thing and not every case of each.
        List<Proposition> withTheLine = new ArrayList<>();
        List<Proposition> againstIt = new ArrayList<>();
        for (List<List<Case>> factors : standings) {
            for (Case way : together(factors.stream().map(WhereEachLineDecides::oneOnEachSide)
                    .toList())) {
                (way.holdsWithTheLine() ? withTheLine : againstIt).add(way.where());
            }
        }
        return heldAndFailing(Proposition.any(withTheLine), Proposition.any(againstIt));
    }

    /** {@code cases} said as one case on each side of the line, where there is one there. */
    private static List<Case> oneOnEachSide(List<Case> cases) {
        return heldAndFailing(
                Proposition.any(cases.stream().filter(Case::holdsWithTheLine)
                        .map(Case::where).toList()),
                Proposition.any(cases.stream().filter(each -> !each.holdsWithTheLine())
                        .map(Case::where).toList()));
    }

    /** A case holding with the line where {@code with} holds and one holding against it where
     *  {@code against} does, leaving out either where it holds nowhere. */
    private static List<Case> heldAndFailing(Proposition with, Proposition against) {
        List<Case> out = new ArrayList<>();
        if (!(with instanceof Proposition.Always(boolean holds) && !holds)) {
            out.add(new Case(with, true));
        }
        if (!(against instanceof Proposition.Always(boolean holds) && !holds)) {
            out.add(new Case(against, false));
        }
        return out;
    }

    /** Every way of taking one case of each of {@code factors} together, or null where there
     *  are more than {@link #MOST_CASES}. */
    private static List<Case> takenTogether(List<List<Case>> factors) {
        long ways = 1;
        for (List<Case> factor : factors) {
            ways *= factor.size();
            if (ways > MOST_CASES) {
                return null;
            }
        }
        return together(factors);
    }

    /**
     * Every way of taking one case of each of {@code factors} together.
     *
     * <p>Each thing the line stands inside turns what holds it one way round or the other, so the
     * statement holds with the line where an even number of them turn it the other way: the
     * statement holding where a quantifier fails, and the quantifier holding where its line fails,
     * is the statement holding where the line holds.
     */
    private static List<Case> together(List<List<Case>> factors) {
        List<Case> ways = List.of(Case.everywhere());
        for (List<Case> factor : factors) {
            List<Case> wider = new ArrayList<>();
            for (Case way : ways) {
                for (Case one : factor) {
                    wider.add(new Case(Proposition.all(List.of(way.where(), one.where())),
                            way.holdsWithTheLine() == one.holdsWithTheLine()));
                }
            }
            ways = wider;
        }
        return ways;
    }

    /** Whether {@code part} stands inside a quantifier {@code stated} joins that it is not about
     *  the element of. */
    private static boolean insideAWholeQuantifier(Proposition stated, Proposition part) {
        return switch (stated) {
            case Proposition.All all -> all.parts().stream()
                    .anyMatch(each -> insideAWholeQuantifier(each, part));
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(each -> insideAWholeQuantifier(each, part));
            case Proposition.Some some when !standsAs(some, part) ->
                    !part.mayTurnOnAnElementOf(some.container())
                            && !with(some.ofTheElement(), part, true).equals(some.ofTheElement());
            default -> false;
        };
    }

    /** Whether {@code leaf} is {@code part}, held or denied. */
    private static boolean standsAs(Proposition leaf, Proposition part) {
        return leaf.getClass() == part.getClass() && held(leaf).key().equals(part.key());
    }

    private static boolean statesARelation(Proposition stated) {
        return switch (stated) {
            case Proposition.Compared _ -> true;
            case Proposition.All all -> all.parts().stream()
                    .anyMatch(WhereEachLineDecides::statesARelation);
            case Proposition.Any any -> any.parts().stream()
                    .anyMatch(WhereEachLineDecides::statesARelation);
            default -> false;
        };
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
            case Proposition.SomeReachable reached -> reached.holds();
            case Proposition.Carried carried -> throw carried.handedToAReader();
            case Proposition.LastToHold last -> last.holds();
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
     *
     * <p>Asked once of the ways where the statement holds with the line and once of the ways where
     * it holds against it, so no case holds some of each. And asked only of the ways the parts can
     * come out together ({@link #possible}): what a way no row is comes to says nothing about
     * where a row has to be.
     */
    private static List<Case> casesOf(boolean[] table, boolean[] possible, int at,
                                      List<Proposition> named) {
        int line = 1 << at;
        boolean[] withTheLine = new boolean[table.length];
        boolean[] againstIt = new boolean[table.length];
        for (int ways = 0; ways < table.length; ways++) {
            if ((ways & line) == 0 && table[ways] != table[ways | line]) {
                withTheLine[ways] = table[ways | line];
                againstIt[ways] = table[ways];
            }
        }
        List<List<Proposition>> cases = new ArrayList<>();
        if (!split(withTheLine, possible, line, 0, 0, new ArrayList<>(), named, at, cases)) {
            return null;
        }
        int held = cases.size();
        if (!split(againstIt, possible, line, 0, 0, new ArrayList<>(), named, at, cases)) {
            return null;
        }
        List<Case> out = new ArrayList<>();
        for (int each = 0; each < cases.size(); each++) {
            out.add(new Case(Proposition.all(cases.get(each)), each < held));
        }
        return out;
    }

    /**
     * The cases under {@code asked}, the parts whose bits are {@code fixed} coming out as
     * {@code values} says — or false as soon as there are more than {@link #MOST_CASES}, so the
     * limit bounds the work and not only what is kept.
     *
     * <p>False as well where no one part tells the ways the line decides at from the rest. Every way
     * being possible, some part always does; with ways no row is left out, the two may be apart in
     * two parts at once, and the cases are not said this way.
     */
    private static boolean split(boolean[] decides, boolean[] possible, int line, int fixed,
                                 int values, List<Proposition> asked, List<Proposition> named,
                                 int at, List<List<Proposition>> into) {
        boolean some = false;
        boolean every = true;
        for (int ways = 0; ways < decides.length; ways++) {
            if ((ways & line) == 0 && (ways & fixed) == values && possible[ways]) {
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
            if (part == at || (fixed & its) != 0
                    || !turnsOn(decides, possible, line, fixed, values, its)) {
                continue;
            }
            List<Proposition> held = new ArrayList<>(asked);
            held.add(named.get(part));
            if (!split(decides, possible, line, fixed | its, values | its, held, named, at,
                    into)) {
                return false;
            }
            List<Proposition> failing = new ArrayList<>(asked);
            failing.add(named.get(part).denied());
            return split(decides, possible, line, fixed | its, values, failing, named, at, into);
        }
        return false;
    }

    /** Whether, the parts at {@code fixed} coming out as {@code values}, where the line decides
     *  turns on the part at {@code its} between two ways both possible. */
    private static boolean turnsOn(boolean[] decides, boolean[] possible, int line, int fixed,
                                   int values, int its) {
        for (int ways = 0; ways < decides.length; ways++) {
            if ((ways & line) == 0 && (ways & its) == 0 && (ways & fixed) == values
                    && possible[ways] && possible[ways | its]
                    && decides[ways] != decides[ways | its]) {
                return true;
            }
        }
        return false;
    }

    /**
     * Which ways the parts can come out together, the {@code i}th part held where bit {@code i}
     * is set.
     *
     * <p>Two parts that say which cases one value of the input is are not free of each other. The
     * value is no two cases that share none, and being one case, it is every set of cases that one
     * is in. A way asking otherwise is one no row is. Kept in the table, it is a way where a line
     * decides or does not, and what tells it from the rest is asked as a part:
     * {@code month.value <= minimum(term)} states its line at 12 where {@code term} is
     * {@code OneYear} and its line at 24 where it is {@code TwoYear}, and with a way where it is
     * both, the line at 12 decided only where the month is not above 24 as well.
     */
    private static boolean[] possible(List<Proposition> named) {
        List<int[]> neverBoth = new ArrayList<>();
        List<int[]> neverFirstAlone = new ArrayList<>();
        for (int one = 0; one < named.size(); one++) {
            for (int other = 0; other < named.size(); other++) {
                if (one != other && named.get(one) instanceof Proposition.InCases first
                        && named.get(other) instanceof Proposition.InCases second
                        && first.holds() && second.holds() && first.of().equals(second.of())) {
                    if (first.cases().meet(second.cases()) == null) {
                        neverBoth.add(new int[] {one, other});
                    } else if (first.cases().within(second.cases())) {
                        neverFirstAlone.add(new int[] {one, other});
                    }
                }
            }
        }
        boolean[] out = new boolean[1 << named.size()];
        for (int ways = 0; ways < out.length; ways++) {
            boolean can = true;
            for (int[] pair : neverBoth) {
                can &= ((ways >> pair[0]) & 1) == 0 || ((ways >> pair[1]) & 1) == 0;
            }
            for (int[] pair : neverFirstAlone) {
                can &= ((ways >> pair[0]) & 1) == 0 || ((ways >> pair[1]) & 1) == 1;
            }
            out[ways] = can;
        }
        return out;
    }

    /**
     * Where {@code part} decides, said as the statement with it held against the statement with it
     * failing: the first holding and the second not, where the statement holds with the part, and
     * the other way round where it holds against it.
     *
     * <p>Only the sides the part can turn the statement to. A statement that states the part held
     * and nowhere denied holds with it wherever it holds without it, so it never holds against it,
     * and the other way round; said anyway, that side is a conjunction of something and its denial
     * that nothing here takes apart, and a reader composing rows against it looks for a row no
     * value is.
     */
    private static List<Case> heldAgainstItsDenial(Proposition stated, Proposition part) {
        Proposition held = with(stated, part, true);
        Proposition failing = with(stated, part, false);
        Set<Boolean> stands = new HashSet<>();
        standings(stated, part, true, stands);
        return heldAndFailing(
                stands.contains(true) ? Proposition.all(List.of(held, failing.denied()))
                        : new Proposition.Always(false),
                stands.contains(false) ? Proposition.all(List.of(held.denied(), failing))
                        : new Proposition.Always(false));
    }

    /**
     * Where {@code part} decides in a statement too large to read part against part, read in each
     * case of one value the statement asks the case of — or null where it asks no value's case
     * twice.
     *
     * <p>The cases of one value are never two at once, and a table of the whole statement is too
     * large to leave out the ways where they are. Read under each case of the value instead, every
     * part asking which case it is comes out one way, and what is left is a statement of the parts
     * that case has: {@code days <= limit(s)} with {@code limit} choosing one of eight numbers is,
     * where {@code s} is the sixth stage, {@code days <= 20} and nothing else. And past every case
     * the statement names, the value being none of them.
     */
    private static List<Case> inEachCaseOfAValue(Proposition stated, List<Proposition> named,
                                                 Proposition part) {
        Map<DecisionSubject, List<Refinement>> asked = new LinkedHashMap<>();
        Map<DecisionSubject, Integer> times = new LinkedHashMap<>();
        for (Proposition each : named) {
            if (each instanceof Proposition.InCases cases && cases.holds()
                    && cases.of() instanceof DecisionSubject.AnInput(TermPath at)
                    && at.steps().stream().noneMatch(step -> step instanceof TermPath.Step.Element
                            || step instanceof TermPath.Step.Key)) {
                times.merge(cases.of(), 1, Integer::sum);
                List<Refinement> atoms = asked.computeIfAbsent(cases.of(), _ -> new ArrayList<>());
                cases.cases().atoms().stream().filter(atom -> !atoms.contains(atom))
                        .forEach(atoms::add);
            }
        }
        DecisionSubject value = times.entrySet().stream().filter(each -> each.getValue() > 1)
                .map(Map.Entry::getKey).findFirst().orElse(null);
        if (value == null) {
            return null;
        }
        List<Refinement> atoms = asked.get(value);
        List<Case> out = new ArrayList<>();
        for (Refinement atom : atoms) {
            Proposition is = new Proposition.InCases(value, CasesLeft.of(atom), true);
            if (!underACase(out, is, assuming(stated, value, List.of(atom)), part)) {
                return null;
            }
        }
        Proposition none = new Proposition.InCases(value, CasesLeft.ofEach(atoms), false);
        if (!underACase(out, none, assuming(stated, value, List.of()), part)) {
            return null;
        }
        return out.size() <= MOST_CASES ? out : null;
    }

    /**
     * Adds to {@code into} where {@code part} decides in {@code stated}, each case said with
     * {@code is} beside it — or false where that was not read.
     */
    private static boolean underACase(List<Case> into, Proposition is, Proposition stated,
                                      Proposition part) {
        Reading reading = Reading.of(stated);
        if (reading.named().stream().noneMatch(each -> each.key().equals(part.key()))) {
            return true;
        }
        for (Case each : reading.turnsOn(part)) {
            into.add(new Case(Proposition.all(List.of(is, each.where())),
                    each.holdsWithTheLine()));
            if (into.size() > MOST_CASES) {
                return false;
            }
        }
        return true;
    }

    /**
     * {@code stated} with {@code value} one of {@code atoms} — every part asking which case it is
     * come out the way that answers — or none of the cases asked where {@code atoms} is empty.
     */
    private static Proposition assuming(Proposition stated, DecisionSubject value,
                                        List<Refinement> atoms) {
        return switch (stated) {
            case Proposition.All all -> Proposition.all(all.parts().stream()
                    .map(each -> assuming(each, value, atoms)).toList());
            case Proposition.Any any -> Proposition.any(any.parts().stream()
                    .map(each -> assuming(each, value, atoms)).toList());
            case Proposition.InCases cases when cases.of().equals(value) -> new Proposition.Always(
                    atoms.stream().anyMatch(cases.cases().atoms()::contains) == cases.holds());
            case Proposition.Some some -> new Proposition.Some(some.container(),
                    assuming(some.ofTheElement(), value, atoms), some.holds());
            default -> stated;
        };
    }

    /**
     * Adds to {@code into} whether {@code part} stands held, denied or both in {@code stated}, each
     * place {@code with} would set it, read from outside where it stands {@code outside}.
     *
     * <p>A quantifier denied is no element meeting what it says, so what it says stands the other
     * way round from it.
     */
    private static void standings(Proposition stated, Proposition part, boolean outside,
                                  Set<Boolean> into) {
        switch (stated) {
            case Proposition.All all ->
                    all.parts().forEach(each -> standings(each, part, outside, into));
            case Proposition.Any any ->
                    any.parts().forEach(each -> standings(each, part, outside, into));
            case Proposition leaf when standsAs(leaf, part) ->
                    into.add(leaf.key().equals(part.key()) == outside);
            case Proposition.Some some when !part.mayTurnOnAnElementOf(some.container()) ->
                    standings(some.ofTheElement(), part, outside == some.holds(), into);
            default -> { }
        }
    }

    /**
     * {@code stated} with every place {@code part} stands come out {@code holds}.
     *
     * <p>Inside a quantifier too, where the part is not about the element it chose: there it is
     * the same thing of the same row. Where it may be about that element it is said of another
     * element, which the part does not move.
     */
    private static Proposition with(Proposition stated, Proposition part, boolean holds) {
        return switch (stated) {
            case Proposition.All all -> Proposition.all(all.parts().stream()
                    .map(each -> with(each, part, holds)).toList());
            case Proposition.Any any -> Proposition.any(any.parts().stream()
                    .map(each -> with(each, part, holds)).toList());
            case Proposition leaf when standsAs(leaf, part) ->
                    new Proposition.Always(leaf.key().equals(part.key()) == holds);
            case Proposition.Some some when !part.mayTurnOnAnElementOf(some.container()) ->
                    new Proposition.Some(some.container(), with(some.ofTheElement(), part, holds),
                            some.holds());
            default -> stated;
        };
    }
}
