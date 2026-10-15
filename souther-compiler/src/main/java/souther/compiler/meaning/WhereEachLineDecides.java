package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Arrays;
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
            cases = DecidingCase.eachByItsOwnCondition(cases);
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
        // Two cases told apart only by what they asked of another case of the value are one case
        // now, said by one condition.
        return DecidingCase.oneForEachCondition(out);
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
        private final boolean[] possible;
        /** Whether some part has asked for the statement under each case of a value. */
        private boolean readUnderEachCase;
        /** The statement under each case of a value, once some part asked for it — null where it
         *  asks no value's case twice. */
        private List<UnderACase> underEachCase;

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
         * same row, and comes out the way the part does. Said as one case then, which moves it
         * everywhere it stands.
         *
         * <p>Where the table says nothing — there is none, or more cases than are said one by one
         * — the statement is read under each case of a value it asks the case of, which leaves out
         * the ways where the value is two cases as the table does; and only past that as one case.
         *
         * <p>Said as one, it stands for the cases it is said for: the ones the table was taken
         * apart into, or the ones read under each case of a value — or, where the table holds more
         * than are taken apart, the fact that there were more.
         */
        List<DecidingCase> turnsOn(Proposition part) {
            if (insideAWholeQuantifier(stated, part)) {
                return List.of(DecidingCase.alone(heldAgainstItsDenial(stated, part)));
            }
            // Taken apart as far as is said one by one first, and further only where nothing short
            // of that says them: every case found walks the table again.
            OffTheTable few = offTheTable(part, MOST_CASES);
            if (few instanceof OffTheTable.Taken(var cases)) {
                return cases.stream().map(each -> DecidingCase.alone(Proposition.all(each)))
                        .toList();
            }
            if (!readUnderEachCase) {
                underEachCase = WhereEachLineDecides.underEachCase(stated, named);
                readUnderEachCase = true;
            }
            List<DecidingCase> ofAValue = underEachCase == null ? null
                    : inEachCaseOfAValue(underEachCase, part);
            if (ofAValue != null && ofAValue.size() <= MOST_CASES) {
                return ofAValue;
            }
            Proposition said = heldAgainstItsDenial(stated, part);
            if (few instanceof OffTheTable.MoreThan) {
                switch (offTheTable(part,
                        CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum())) {
                    case OffTheTable.Taken(var cases) -> {
                        return List.of(new DecidingCase(said,
                                DecidingCase.Cases.ofConjunctions(cases)));
                    }
                    case OffTheTable.MoreThan _ -> {
                        return List.of(new DecidingCase(said,
                                new DecidingCase.Cases.MoreThanWereTakenApart()));
                    }
                    case OffTheTable.NotSaidThisWay _ -> { }
                }
            }
            return List.of(ofAValue == null ? DecidingCase.alone(said)
                    : new DecidingCase(said, DecidingCase.eachOf(ofAValue)));
        }

        /** Where {@code part} decides, as the table says it, taken apart into {@code most} cases
         *  at most. */
        private OffTheTable offTheTable(Proposition part, int most) {
            return table == null ? new OffTheTable.NotSaidThisWay()
                    : casesOf(table, possible, index.get(part.key()), named, most);
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
        List<DecidingCase> cases = new ArrayList<>();
        boolean saidOneByOne = true;
        for (List<List<DecidingCase>> factors : standings) {
            List<DecidingCase> here = takenTogether(factors);
            if (here == null) {
                saidOneByOne = false;
                break;
            }
            cases.addAll(here);
        }
        List<DecidingCase> each = saidOneByOne
                ? joinedOverAValue(DecidingCase.oneForEachCondition(cases)) : null;
        if (each != null && each.size() <= MOST_CASES) {
            return each;
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
     * Where a line decides, as the table says it: the cases, each the parts it asks; more than
     * were taken apart; or not said this way at all.
     *
     * <p>Three answers and not a list that is sometimes long and sometimes absent. More cases
     * than a figure lets be taken apart is a stop at that figure, and a table that says them no
     * way it can is something about the statement; told apart by how many cases came back, the
     * two were one reading's guess about the other.
     */
    private sealed interface OffTheTable {

        /** The cases, each the parts it asks. */
        record Taken(List<List<Proposition>> cases) implements OffTheTable {

            public Taken {
                cases = List.copyOf(cases);
            }
        }

        /** More cases than were taken apart. */
        record MoreThan() implements OffTheTable {}

        /** Not said off the table: there is none, or no one part tells where the line decides from
         *  the rest ({@link #split}). */
        record NotSaidThisWay() implements OffTheTable {}
    }

    /**
     * How a taking apart of the table ({@link #split}) stopped, where it did not come to the end.
     */
    private enum Stopped {
        /** At the end, every case taken. */
        NOT,
        /** One case past the figure. */
        PAST_THE_FIGURE,
        /** Where no one part tells the ways the line decides at from the rest. */
        BY_NO_ONE_PART
    }

    /**
     * Where the {@code at}th part decides, read off what the statement comes to every way its parts
     * can come out, taken apart into {@code most} cases at most.
     *
     * <p>The line decides at a way its other parts come out where the statement comes out
     * differently with the line held and with it failing. The cases are taken by asking the other
     * parts one at a time, in order, each only where what is left still turns on it: a part every
     * way left decides under, or none does, says nothing more.
     *
     * <p>Asked only of the ways the parts can come out together ({@link #possible}): what a way no
     * row is comes to says nothing about where a row has to be.
     */
    private static OffTheTable casesOf(boolean[] table, boolean[] possible, int at,
                                       List<Proposition> named, int most) {
        int line = 1 << at;
        boolean[] decides = new boolean[table.length];
        for (int ways = 0; ways < table.length; ways++) {
            decides[ways] = (ways & line) == 0 && table[ways] != table[ways | line];
        }
        List<List<Proposition>> cases = new ArrayList<>();
        return switch (split(decides, possible, line, 0, 0, new ArrayList<>(), named, at, most,
                cases)) {
            case NOT -> new OffTheTable.Taken(cases);
            case PAST_THE_FIGURE -> new OffTheTable.MoreThan();
            case BY_NO_ONE_PART -> new OffTheTable.NotSaidThisWay();
        };
    }

    /**
     * The cases under {@code asked}, the parts whose bits are {@code fixed} coming out as
     * {@code values} says — stopped as soon as there are more than {@code most}, so the limit
     * bounds the work and not only what is kept.
     *
     * <p>Stopped as well where no one part tells the ways the line decides at from the rest. Every
     * way being possible, some part always does; with ways no row is left out, the two may be apart
     * in two parts at once, and the cases are not said this way.
     */
    private static Stopped split(boolean[] decides, boolean[] possible, int line, int fixed,
                                 int values, List<Proposition> asked, List<Proposition> named,
                                 int at, int most, List<List<Proposition>> into) {
        boolean some = false;
        boolean every = true;
        for (int ways = 0; ways < decides.length; ways++) {
            if ((ways & line) == 0 && (ways & fixed) == values && possible[ways]) {
                some |= decides[ways];
                every &= decides[ways];
            }
        }
        if (!some) {
            return Stopped.NOT;
        }
        if (every) {
            into.add(List.copyOf(asked));
            return into.size() <= most ? Stopped.NOT : Stopped.PAST_THE_FIGURE;
        }
        for (int part = 0; part < named.size(); part++) {
            int its = 1 << part;
            if (part == at || (fixed & its) != 0
                    || !turnsOn(decides, possible, line, fixed, values, its)) {
                continue;
            }
            List<Proposition> held = new ArrayList<>(asked);
            held.add(named.get(part));
            Stopped holding = split(decides, possible, line, fixed | its, values | its, held,
                    named, at, most, into);
            if (holding != Stopped.NOT) {
                return holding;
            }
            List<Proposition> failing = new ArrayList<>(asked);
            failing.add(named.get(part).denied());
            return split(decides, possible, line, fixed | its, values, failing, named, at, most,
                    into);
        }
        return Stopped.BY_NO_ONE_PART;
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
     * <p>Parts that say which cases one value of the input is are not free of each other: the
     * value is one case, so a way is one a row can be only where some one case is in every set of
     * cases held there and in none failing there. Kept in the table, a way where it is two at once
     * is a way where a line decides or does not, and what tells it from the rest is asked as a
     * part: {@code month.value <= minimum(term)} states its line at 12 where {@code term} is
     * {@code OneYear} and its line at 24 where it is {@code TwoYear}, and with a way where it is
     * both, the line at 12 decided only where the month is not above 24 as well.
     *
     * <p>The cases the parts name need not be every case of the value, so a value none of them
     * names is a case as well: every way holding none of them is possible.
     */
    private static boolean[] possible(List<Proposition> named) {
        Map<DecisionSubject, List<Integer>> byValue = new LinkedHashMap<>();
        for (int i = 0; i < named.size(); i++) {
            if (named.get(i) instanceof Proposition.InCases cases && oneValueOfTheRow(cases)) {
                byValue.computeIfAbsent(cases.of(), _ -> new ArrayList<>()).add(i);
            }
        }
        boolean[] out = new boolean[1 << named.size()];
        Arrays.fill(out, true);
        for (List<Integer> parts : byValue.values()) {
            if (parts.size() < 2) {
                continue;
            }
            List<Refinement> atoms = new ArrayList<>();
            for (int each : parts) {
                ((Proposition.InCases) named.get(each)).cases().atoms().stream()
                        .filter(atom -> !atoms.contains(atom)).forEach(atoms::add);
            }
            // Which of the parts hold for a value that is each case, as bits; and none of them
            // for a value that is a case none of them names.
            Set<Integer> holding = new HashSet<>();
            holding.add(0);
            for (Refinement atom : atoms) {
                int bits = 0;
                for (int each : parts) {
                    if (((Proposition.InCases) named.get(each)).cases().atoms().contains(atom)) {
                        bits |= 1 << each;
                    }
                }
                holding.add(bits);
            }
            int mask = parts.stream().mapToInt(each -> 1 << each).reduce(0, (a, b) -> a | b);
            for (int ways = 0; ways < out.length; ways++) {
                out[ways] &= holding.contains(ways & mask);
            }
        }
        return out;
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
     * Where {@code part} decides in a statement the table does not say it of, read in each case
     * of one value the statement asks the case of, which may be more cases than are said one by
     * one.
     *
     * <p>The cases of one value are never two at once, and a statement too large for a table, or
     * one whose table says too much, is read under each case of the value instead: every part
     * asking which case it is comes out one way, and what is left is a statement of the parts
     * that case has. {@code days <= limit(s)} with {@code limit} choosing one of eight numbers is,
     * where {@code s} is the sixth stage, {@code days <= 20} and nothing else. And past every case
     * the statement names, the value being none of them.
     *
     * @param underEachCase the statement read under each case of the value ({@link #underEachCase})
     */
    private static List<DecidingCase> inEachCaseOfAValue(List<UnderACase> underEachCase,
                                                         Proposition part) {
        List<DecidingCase> out = new ArrayList<>();
        for (UnderACase each : underEachCase) {
            if (each.reading().index.containsKey(part.key())) {
                each.reading().turnsOn(part).forEach(one -> out.add(one.meeting(each.is())));
            }
        }
        return joinedOverAValue(out);
    }

    /** A statement read under one case of a value: the case, and the reading of what the
     *  statement comes to there. */
    private record UnderACase(Proposition is, Reading reading) {}

    /**
     * {@code stated} read under each case of the first value it asks the case of more than once,
     * and under that value being none of them — or null where it asks no value's case twice.
     *
     * <p>The same for every part of the statement, so worked out once for the statement and asked
     * of by each of its parts. A value inside the elements or the keys of a container is not one
     * value of the row, and is not read this way.
     */
    private static List<UnderACase> underEachCase(Proposition stated, List<Proposition> named) {
        Map<DecisionSubject, List<Refinement>> asked = new LinkedHashMap<>();
        Map<DecisionSubject, Integer> times = new LinkedHashMap<>();
        for (Proposition each : named) {
            if (each instanceof Proposition.InCases cases && oneValueOfTheRow(cases)) {
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
        List<UnderACase> out = new ArrayList<>();
        for (Refinement atom : atoms) {
            out.add(new UnderACase(new Proposition.InCases(value, CasesLeft.of(atom), true),
                    Reading.of(assuming(stated, value, List.of(atom)))));
        }
        out.add(new UnderACase(new Proposition.InCases(value, CasesLeft.ofEach(atoms), false),
                Reading.of(assuming(stated, value, List.of()))));
        return out;
    }

    /**
     * {@code cases}, each of them where {@code taken} holds as well: where a line of the author's
     * decides that is under arms a row takes only where {@code taken} holds.
     *
     * <p>One relation can be a place of several of the author's lines. {@code minimum(term)} with
     * an arm for each of seventeen terms returning 12 puts one line at 12 under each arm, and the
     * statement turns at 12 for every one of those terms; the line under the first arm turns it
     * only for the first. A case asking a value to be cases the arms do not take is no case of the
     * line, and is left out.
     */
    public static List<DecidingCase> takenWhere(List<DecidingCase> cases, Proposition taken) {
        if (taken instanceof Proposition.Always(boolean holds) && holds) {
            return cases;
        }
        return joinedOverAValue(cases.stream().map(each -> each.meeting(taken)).toList());
    }

    /**
     * {@code stated} with what it asks each value of the row to be said as the cases left: the
     * cases every set it holds the value to shares, less the cases it holds the value out of — or
     * holding nowhere where none is left. A value it only holds out of some cases is left asked
     * that.
     *
     * <p>A case read off the table says the parts asked before it failing beside the one that
     * holds: where the term is not the first case and is the second. Of one value, the first says
     * nothing the second does not, and said apart it keeps two cases that differ in which case the
     * value is from being said as one ({@link #joinedOverAValue}).
     */
    private static Proposition leftOfEachValue(Proposition stated) {
        List<Proposition> parts = stated instanceof Proposition.All all ? all.parts()
                : List.of(stated);
        Map<DecisionSubject, CasesLeft> held = new LinkedHashMap<>();
        Map<DecisionSubject, List<Refinement>> outside = new LinkedHashMap<>();
        List<Proposition> rest = new ArrayList<>();
        for (Proposition part : parts) {
            if (part instanceof Proposition.InCases asked && oneValueOfTheRow(asked)) {
                CasesLeft before = held.get(asked.of());
                CasesLeft both = before == null ? asked.cases() : before.meet(asked.cases());
                if (both == null) {
                    return new Proposition.Always(false);
                }
                held.put(asked.of(), both);
            } else if (part instanceof Proposition.InCases denied && !denied.holds()
                    && aValueOfTheRow(denied.of())) {
                outside.computeIfAbsent(denied.of(), _ -> new ArrayList<>())
                        .addAll(denied.cases().atoms());
            } else {
                rest.add(part);
            }
        }
        outside.forEach((value, atoms) -> {
            if (!held.containsKey(value)) {
                rest.add(new Proposition.InCases(value, CasesLeft.ofEach(atoms), false));
            }
        });
        for (Map.Entry<DecisionSubject, CasesLeft> each : held.entrySet()) {
            List<Refinement> out = outside.getOrDefault(each.getKey(), List.of());
            List<Refinement> left = each.getValue().atoms().stream()
                    .filter(atom -> !out.contains(atom)).toList();
            if (left.isEmpty()) {
                return new Proposition.Always(false);
            }
            rest.add(new Proposition.InCases(each.getKey(), CasesLeft.ofEach(left), true));
        }
        return Proposition.all(rest);
    }

    /**
     * {@code cases}, with every two that ask one value to be two different cases and are the same
     * otherwise said as one asking it to be either: where the value is A and the rest holds, or B
     * and the rest holds, is where it is A or B and the rest holds.
     *
     * <p>The same cases and so the same rows, said in fewer. Asked before what is said is held to
     * {@link #MOST_CASES}, because a line every case of a value turns the same way is one case
     * however many cases the value has: past the bound and read whole instead, it lost which cases
     * those were, and a reader could no longer be told them.
     *
     * <p>A case said for several stands, joined, for each case every one of those joined stood
     * for: what was said for several is kept as several, whatever it was joined with.
     */
    static List<DecidingCase> joinedOverAValue(List<DecidingCase> cases) {
        Map<String, Joined> joined = new LinkedHashMap<>();
        for (DecidingCase written : cases) {
            // Said as the cases left of each value first, so that what two cases ask of a value is
            // one set each and the two are told apart by that alone. A case leaving no value is
            // no case.
            Proposition each = leftOfEachValue(written.condition());
            if (each instanceof Proposition.Always(boolean holds) && !holds) {
                continue;
            }
            List<Proposition> parts = each instanceof Proposition.All all ? all.parts()
                    : List.of(each);
            Proposition.InCases asked = parts.stream()
                    .filter(part -> part instanceof Proposition.InCases in && oneValueOfTheRow(in))
                    .map(Proposition.InCases.class::cast).findFirst().orElse(null);
            if (asked == null) {
                joined.computeIfAbsent("whole " + each.key(),
                        _ -> new Joined(null, each, List.of(), new ArrayList<>()))
                        .written().add(written);
                continue;
            }
            Proposition rest = Proposition.all(parts.stream().filter(part -> part != asked)
                    .toList());
            Joined there = joined.computeIfAbsent(asked.of() + " " + rest.key(),
                    _ -> new Joined(asked.of(), rest, new ArrayList<>(), new ArrayList<>()));
            asked.cases().atoms().stream().filter(atom -> !there.atoms().contains(atom))
                    .forEach(there.atoms()::add);
            there.written().add(written);
        }
        return joined.values().stream().map(Joined::said).toList();
    }

    /** Cases of {@link #joinedOverAValue} that differ in which case {@code value} is alone; a case
     *  asking no value's case where {@code value} is null. */
    private record Joined(DecisionSubject value, Proposition rest, List<Refinement> atoms,
                          List<DecidingCase> written) {

        /**
         * The cases joined, said as one: standing for itself where one of them did, as two said
         * by one condition do ({@link DecidingCase#and}); otherwise for what each stood for with
         * the value's case read as any of the cases joined, since which of them it is tells no
         * two cases apart here.
         */
        DecidingCase said() {
            Proposition said = value == null ? rest : Proposition.all(List.of(
                    new Proposition.InCases(value, CasesLeft.ofEach(atoms), true), rest));
            List<DecidingCase> each = DecidingCase.oneForEachCondition(written);
            if (each.stream().anyMatch(DecidingCase::saidAlone)) {
                return DecidingCase.alone(said);
            }
            List<DecidingCase.Cases> standFor = each.stream()
                    .map(one -> value == null ? one.standsFor()
                            : one.standsFor().eachSaid(this::anyOfTheJoined))
                    .distinct()
                    .toList();
            return new DecidingCase(said, standFor.size() == 1 ? standFor.getFirst()
                    : new DecidingCase.Cases.EachOf(standFor));
        }

        /** {@code one}, asking {@link #value} to be any of the cases joined wherever it asks it to
         *  be some of them — no case at all where it asks for none. */
        private DecidingCase.Cases anyOfTheJoined(Proposition one) {
            Proposition left = leftOfEachValue(one);
            if (left instanceof Proposition.Always(boolean holds) && !holds) {
                return new DecidingCase.Cases.EachOf(List.of());
            }
            List<Proposition> parts = new ArrayList<>();
            for (Proposition part : left instanceof Proposition.All all ? all.parts()
                    : List.of(left)) {
                parts.add(part instanceof Proposition.InCases asked && oneValueOfTheRow(asked)
                        && asked.of().equals(value)
                        ? new Proposition.InCases(value, CasesLeft.ofEach(atoms), true) : part);
            }
            return new DecidingCase.Cases.One(Proposition.all(parts));
        }
    }

    /**
     * Whether {@code cases}, held, asks which case one value of the row is. A value inside the
     * elements or the keys of a container is one of them, and two parts asking it may ask it of two
     * elements.
     */
    private static boolean oneValueOfTheRow(Proposition.InCases cases) {
        return cases.holds() && aValueOfTheRow(cases.of());
    }

    /** Whether {@code value} is one value of the row, and not one inside the elements or the keys
     *  of a container. */
    private static boolean aValueOfTheRow(DecisionSubject value) {
        return value instanceof DecisionSubject.AnInput(TermPath at)
                && at.steps().stream().noneMatch(step -> step instanceof TermPath.Step.Element
                        || step instanceof TermPath.Step.Key);
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
