package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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

    /**
     * How many cases where a line decides is said in before it is said as one.
     *
     * <p>How many are said, and not which: the cases said as one are kept beside it
     * ({@link DecidingCase#standsFor}), so whether the line decides in any of them is asked of
     * them and not of the one condition they were said as.
     */
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
    public record Decides(Proposition.Compared line, List<DecidingCase> cases) {

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
        Map<String, List<List<List<DecidingCase>>>> standings = new TreeMap<>();
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
     *
     * <p>And so is every case one said for several stands for, part by part where it was taken
     * apart: a part is asked of the value whichever case it is chosen in, so a case is what its
     * parts come to however it was put together.
     */
    private static List<DecidingCase> whereItStands(Proposition.Compared line,
                                                    List<DecidingCase> cases) {
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
        Proposition standsThere = Proposition.all(stands);
        List<DecidingCase> out = new ArrayList<>();
        for (DecidingCase each : cases) {
            Proposition there = there(each.condition(), at);
            if (there == null) {
                continue;
            }
            Proposition said = Proposition.all(List.of(there, standsThere));
            out.add(each.saidAlone() ? DecidingCase.alone(said) : new DecidingCase(said,
                    new DecidingCase.Cases.Together(List.of(each.standsFor().eachSaid(one -> {
                        Proposition itsOwn = there(one, at);
                        return itsOwn == null ? new DecidingCase.Cases.EachOf(List.of())
                                : new DecidingCase.Cases.One(itsOwn);
                    }), new DecidingCase.Cases.One(standsThere)))));
        }
        return out;
    }

    /**
     * {@code each}, without the parts of it that ask the value the line is at what only another
     * case of it has — or null where a part of it asks the value to be a case it is not.
     */
    private static Proposition there(Proposition each, Map<TermPath, CasesLeft> at) {
        List<Proposition> parts = new ArrayList<>();
        for (Proposition part : each instanceof Proposition.All all ? all.parts()
                : List.of(each)) {
            switch (asked(part, at)) {
                case OF_ANOTHER_CASE -> { }
                case NOT_THERE -> {
                    return null;
                }
                case THERE -> parts.add(part);
            }
        }
        return Proposition.all(parts);
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
                             List<List<DecidingCase>> around,
                             Map<String, Proposition.Compared> lines,
                             Map<String, List<List<List<DecidingCase>>>> standings) {
        Reading reading = Reading.of(stated);
        for (Proposition part : reading.named()) {
            if (part instanceof Proposition.Compared line) {
                List<List<DecidingCase>> factors = new ArrayList<>(around);
                if (element == null || line.mayTurnOnAnElementOf(element)) {
                    factors.add(reading.turnsOn(line));
                } else {
                    factors = List.of(List.of(
                            DecidingCase.alone(heldAgainstItsDenial(whole, line))));
                }
                lines.putIfAbsent(line.key(), line);
                standings.computeIfAbsent(line.key(), k -> new ArrayList<>()).add(factors);
            } else if (part instanceof Proposition.Some some && reading.standsHeld(some)
                    && statesARelation(some.ofTheElement())) {
                List<List<DecidingCase>> inside = new ArrayList<>(around);
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

        private Reading(Proposition stated, List<Proposition> named, Map<String, Integer> index,
                        Map<String, Literal> leaves, boolean[] table) {
            this.stated = stated;
            this.named = named;
            this.index = index;
            this.leaves = leaves;
            this.table = table;
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
            return new Reading(stated, named, index, leaves, table);
        }

        /**
         * Where {@code part} turns the statement, as cases.
         *
         * <p>The table holds each part as one thing that comes out one way, which a part standing
         * as well inside a quantifier it is not about is not: there it is the same thing of the
         * same row, and comes out the way the part does. Said as one case then, which moves it
         * everywhere it stands.
         *
         * <p>Past {@link #MOST_CASES}, said as one case too, and the cases it is said for kept
         * beside it — or, past as many as are taken apart, the fact that there were more.
         */
        List<DecidingCase> turnsOn(Proposition part) {
            if (table == null || insideAWholeQuantifier(stated, part)) {
                return List.of(DecidingCase.alone(heldAgainstItsDenial(stated, part)));
            }
            List<List<Proposition>> cases = casesOf(table, index.get(part.key()), named,
                    CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum());
            if (cases != null && cases.size() <= MOST_CASES) {
                return cases.stream().map(each -> DecidingCase.alone(Proposition.all(each)))
                        .toList();
            }
            return List.of(new DecidingCase(heldAgainstItsDenial(stated, part), cases == null
                    ? new DecidingCase.Cases.MoreThanWereTakenApart()
                    : DecidingCase.Cases.ofConjunctions(cases)));
        }

        /** Whether {@code quantifier} stands held somewhere in the statement. */
        boolean standsHeld(Proposition.Some quantifier) {
            return leaves.values().stream().anyMatch(leaf ->
                    leaf.held() && leaf.part().equals(quantifier.key()));
        }
    }

    /**
     * Where a line decides, off each way it stands: a case of what each thing around it is turned
     * under, taken together — or, where those are more than {@link #MOST_CASES}, each way said as
     * one case, which stands for the ways it was said for.
     */
    private static List<DecidingCase> casesOf(List<List<List<DecidingCase>>> standings) {
        Map<Proposition, DecidingCase> cases = new LinkedHashMap<>();
        boolean saidOneByOne = true;
        for (List<List<DecidingCase>> factors : standings) {
            List<DecidingCase> here = takenTogether(factors);
            if (here == null) {
                saidOneByOne = false;
                break;
            }
            here.forEach(each -> cases.putIfAbsent(each.condition(), each));
        }
        if (saidOneByOne && cases.size() <= MOST_CASES) {
            return List.copyOf(cases.values());
        }
        return List.of(new DecidingCase(
                Proposition.any(standings.stream()
                        .map(factors -> Proposition.all(factors.stream()
                                .map(factor -> Proposition.any(factor.stream()
                                        .map(DecidingCase::condition).toList()))
                                .toList()))
                        .toList()),
                new DecidingCase.Cases.EachOf(standings.stream()
                        .<DecidingCase.Cases>map(factors -> new DecidingCase.Cases.Together(
                                factors.stream()
                                        .<DecidingCase.Cases>map(factor ->
                                                new DecidingCase.Cases.EachOf(factor.stream()
                                                        .map(DecidingCase::standsFor).toList()))
                                        .toList()))
                        .toList())));
    }

    /** Every way of taking one case of each of {@code factors} together, or null as soon as
     *  there are more than {@link #MOST_CASES}. */
    private static List<DecidingCase> takenTogether(List<List<DecidingCase>> factors) {
        List<List<DecidingCase>> ways = List.of(List.of());
        for (List<DecidingCase> factor : factors) {
            if ((long) ways.size() * factor.size() > MOST_CASES) {
                return null;
            }
            List<List<DecidingCase>> wider = new ArrayList<>();
            for (List<DecidingCase> way : ways) {
                for (DecidingCase one : factor) {
                    List<DecidingCase> both = new ArrayList<>(way);
                    both.add(one);
                    wider.add(both);
                }
            }
            ways = wider;
        }
        return ways.stream().map(WhereEachLineDecides::together).toList();
    }

    /** One case of each of several taken together: the case itself where each was said alone,
     *  and otherwise said for the cases of each taken together. */
    private static DecidingCase together(List<DecidingCase> chosen) {
        Proposition said = Proposition.all(chosen.stream().map(DecidingCase::condition).toList());
        return chosen.stream().allMatch(DecidingCase::saidAlone) ? DecidingCase.alone(said)
                : new DecidingCase(said, new DecidingCase.Cases.Together(
                        chosen.stream().map(DecidingCase::standsFor).toList()));
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
     * can come out, as cases, each the parts it asks — or null where there are more of them than
     * {@code most}.
     *
     * <p>The line decides at a way its other parts come out where the statement comes out
     * differently with the line held and with it failing. The cases are taken by asking the other
     * parts one at a time, in order, each only where what is left still turns on it: a part every
     * way left decides under, or none does, says nothing more.
     */
    private static List<List<Proposition>> casesOf(boolean[] table, int at,
                                                   List<Proposition> named, int most) {
        int line = 1 << at;
        boolean[] decides = new boolean[table.length];
        for (int ways = 0; ways < table.length; ways++) {
            decides[ways] = (ways & line) == 0 && table[ways] != table[ways | line];
        }
        List<List<Proposition>> cases = new ArrayList<>();
        if (!split(decides, line, 0, 0, new ArrayList<>(), named, at, most, cases)) {
            return null;
        }
        return cases;
    }

    /**
     * The cases under {@code asked}, the parts whose bits are {@code fixed} coming out as
     * {@code values} says — or false as soon as there are more than {@code most}, so the limit
     * bounds the work and not only what is kept.
     */
    private static boolean split(boolean[] decides, int line, int fixed, int values,
                                 List<Proposition> asked, List<Proposition> named, int at,
                                 int most, List<List<Proposition>> into) {
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
            return into.size() <= most;
        }
        for (int part = 0; part < named.size(); part++) {
            int its = 1 << part;
            if (part == at || (fixed & its) != 0 || !turnsOn(decides, line, fixed, values, its)) {
                continue;
            }
            List<Proposition> held = new ArrayList<>(asked);
            held.add(named.get(part));
            if (!split(decides, line, fixed | its, values | its, held, named, at, most, into)) {
                return false;
            }
            List<Proposition> failing = new ArrayList<>(asked);
            failing.add(named.get(part).denied());
            return split(decides, line, fixed | its, values, failing, named, at, most, into);
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
     * Where {@code part} decides, said as the statement with it held against the statement with it
     * failing: one of them holding and the other not.
     */
    private static Proposition heldAgainstItsDenial(Proposition stated, Proposition part) {
        Proposition held = with(stated, part, true);
        Proposition failing = with(stated, part, false);
        return Proposition.any(List.of(
                Proposition.all(List.of(held, failing.denied())),
                Proposition.all(List.of(held.denied(), failing))));
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
