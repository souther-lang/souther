package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
     * How many cases where a line decides is said in before it is said as one.
     *
     * <p>How many are said, and not which: the cases said as one are kept beside it
     * ({@link DecidingCase#standsFor}), so whether the line decides in any of them is asked of
     * them and not of the one condition they were said as.
     */
    public static final int MOST_CASES = 16;

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
     * @param scales the line held at every scale the statement wrote it at, {@code line} first:
     *               what made each of them made the line, which the statement holds at the first
     */
    public record Decides(Proposition.Compared line, List<DecidingCase> cases,
                          List<Proposition.Compared> scales) {

        public Decides {
            Objects.requireNonNull(line, "a line is some relation");
            cases = DecidingCase.eachByItsOwnCondition(cases);
            scales = List.copyOf(scales);
            if (!line.holds()) {
                throw new IllegalArgumentException("a line is the relation held: " + line);
            }
            if (scales.isEmpty() || !scales.getFirst().equals(line)
                    || !scales.stream().allMatch(Proposition.Compared::holds)) {
                throw new IllegalArgumentException("a line is written at its own scale first, and"
                        + " held at each: " + line + " at " + scales);
            }
        }
    }

    /**
     * Every relation {@code stated} holds together, once each and in the order of their spellings,
     * with where each decides.
     *
     * <p>Only the relations that a conjunction or a disjunction joins, and the ones a quantifier
     * says of the element it chose. What a closure says on each application is one part here, and
     * a count of statements is read as a count: its statements are the parts, and what it comes to
     * is built from the number that hold. A count inside a quantifier is handed in with its counts
     * written out as the choices of which statements hold ({@link CountsWrittenOut}).
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
     *
     * <p>Read with every part a quantifier holds that is about no element it chose said outside it
     * ({@link Lifting}), so that each part is one part of what it stands in. Where that is more
     * than is read, nothing is taken apart, and every line is where its statement turns, said for
     * cases nobody took apart.
     */
    public static List<Decides> in(Proposition writtenAs) {
        Map<String, Proposition.Compared> lines = new TreeMap<>();
        Map<String, List<List<List<DecidingCase>>>> standings = new TreeMap<>();
        OneSpellingPerLine spellings = new OneSpellingPerLine();
        Proposition stated = spellings.of(writtenAs);
        Proposition lifted = new Lifting().of(stated);
        if (lifted != null) {
            read(lifted, lifted, null, List.of(), true, lines, standings);
        } else {
            read(stated, stated, null, List.of(), false, lines, standings);
        }
        List<Decides> out = new ArrayList<>();
        lines.forEach((key, line) -> out.add(new Decides(line,
                whereItStands(line, casesOf(standings.get(key))), spellings.scalesOf(line))));
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
            case Proposition.Truth _, Proposition.InCases _, Proposition.Present _,
                 Proposition.Always _, Proposition.SameValue _, Proposition.LastToHold _,
                 Proposition.All _, Proposition.Any _, Proposition.Some _, Proposition.Carried _,
                 Proposition.SomeReachable _, Proposition.Unread _,
                 Proposition.OnAnApplication _, Proposition.WhereItAnswers _ -> { }
            case Proposition.SoManyHold counted -> throw notWrittenOut(counted);
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
     * quantifier it joins that says a relation of the element it chose, each with how it stands:
     * where each thing around it turns what holds it, outermost first, and where it turns what it
     * stands in. A quantifier the statement denies is one it joins as well: no element meeting a
     * relation turns at the relation where some element meeting it does.
     *
     * <p>A relation inside a quantifier and not about the element it chose is about the row, and
     * stands wherever it is written. Lifted out of the quantifier, it is a part of what holds the
     * quantifier and is read there; only where the statement was more than is lifted does it stand
     * inside one still, and then it is asked of the statement whole, every quantifier it stands in
     * moved with it — as nothing taken apart, since nothing is.
     *
     * @param whole   the statement as written
     * @param element the container whose element {@code stated} is said of, or null where
     *                {@code stated} is the statement itself
     * @param around  where each quantifier {@code stated} is inside turns what holds it
     * @param lifted  whether every part a quantifier holds that is about no element it chose was
     *                said outside it ({@link Lifting}), and so whether the statement is read at all
     */
    private static void read(Proposition stated, Proposition whole, DecisionSubject element,
                             List<List<DecidingCase>> around, boolean lifted,
                             Map<String, Proposition.Compared> lines,
                             Map<String, List<List<List<DecidingCase>>>> standings) {
        Reading reading = lifted ? Reading.of(stated) : Reading.unread(stated);
        Set<String> whereItAnswers = onlyWhereItAnswers(stated);
        for (Proposition part : reading.named()) {
            if (part instanceof Proposition.Compared line
                    && !whereItAnswers.contains(line.key())) {
                List<List<DecidingCase>> factors = new ArrayList<>(around);
                if (element == null || line.mayTurnOnAnElementOf(element)) {
                    factors.add(reading.turnsOn(line));
                } else if (lifted) {
                    throw new IllegalStateException(line + " is about no element of " + element
                            + ", and was not lifted out of the quantifier over it");
                } else {
                    factors = List.of(Reading.unread(whole).turnsOn(line));
                }
                lines.putIfAbsent(line.key(), line);
                standings.computeIfAbsent(line.key(), k -> new ArrayList<>()).add(factors);
            } else if (part instanceof Proposition.Some some
                    && statesARelation(some.ofTheElement())) {
                List<List<DecidingCase>> inside = new ArrayList<>(around);
                inside.add(reading.turnsOn(some));
                read(some.ofTheElement(), whole, some.container(), inside, lifted, lines,
                        standings);
            }
        }
    }

    /**
     * A statement with every relation it holds at more than one scale written at the first: {@code
     * 2c >= 0} and {@code c >= 0} are one line. Read as two, crossing nought turns both at once, and
     * neither of them turns the statement alone.
     *
     * <p>Here and not in how a relation is written down, because which scale a relation was written
     * at is what a reader of a document is shown and what a row is found against; only that two of
     * them are one line is this reading's. A statement holding each line at one scale is itself.
     */
    private static final class OneSpellingPerLine {

        /** A relation and the atoms it is over, which every scale of one line shares. */
        private record Alike(Rel proposition, Set<Quantity> atoms) {}

        private final Map<Alike, List<Relation.Affine>> written = new HashMap<>();
        /** Each relation written first, and every scale it was written at, itself first. */
        private final Map<Relation.Affine, List<Relation.Affine>> scales = new HashMap<>();

        /** {@code line} held at every scale the statement wrote it at, itself first. */
        List<Proposition.Compared> scalesOf(Proposition.Compared line) {
            if (!(line.relation() instanceof Relation.Affine affine)
                    || !scales.containsKey(affine)) {
                return List.of(line);
            }
            return scales.get(affine).stream()
                    .map(each -> new Proposition.Compared(each, true)).toList();
        }

        Proposition of(Proposition stated) {
            return switch (stated) {
                case Proposition.All all -> {
                    List<Proposition> parts = each(all.parts());
                    yield parts == all.parts() ? stated : Proposition.all(parts);
                }
                case Proposition.Any any -> {
                    List<Proposition> parts = each(any.parts());
                    yield parts == any.parts() ? stated : Proposition.any(parts);
                }
                case Proposition.Some some -> {
                    Proposition element = of(some.ofTheElement());
                    yield element == some.ofTheElement() ? stated
                            : new Proposition.Some(some.container(), element, some.holds());
                }
                case Proposition.WhereItAnswers where -> {
                    Proposition answers = of(where.answers());
                    Proposition states = of(where.states());
                    yield answers == where.answers() && states == where.states() ? stated
                            : Proposition.whereItAnswers(answers, states);
                }
                case Proposition.Compared(Relation.Affine affine, boolean holds, String _) -> {
                    Relation.Affine first = firstWritten(affine);
                    yield first == affine ? stated : new Proposition.Compared(first, holds);
                }
                case Proposition.SoManyHold counted -> counted.mapped(this::of);
                case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                     Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                     Proposition.LastToHold _, Proposition.Carried _, Proposition.SomeReachable _,
                     Proposition.Unread _, Proposition.OnAnApplication _ -> stated;
            };
        }

        private List<Proposition> each(List<Proposition> parts) {
            List<Proposition> out = new ArrayList<>();
            boolean changed = false;
            for (Proposition part : parts) {
                Proposition said = of(part);
                changed |= said != part;
                out.add(said);
            }
            return changed ? out : parts;
        }

        /** The relation {@code affine} is at the scale it was first written, which is itself where
         *  it is the first. Both face one way, so one is the other at a positive scale. */
        private Relation.Affine firstWritten(Relation.Affine affine) {
            List<Relation.Affine> alike = written.computeIfAbsent(
                    new Alike(affine.proposition(), affine.form().coefs().keySet()),
                    _ -> new ArrayList<>());
            for (Relation.Affine each : alike) {
                ExactRatio scale = affine.form().multipleOf(each.form());
                if (scale != null && scale.signum() > 0) {
                    List<Relation.Affine> atEach = scales.get(each);
                    if (!atEach.contains(affine)) {
                        atEach.add(affine);
                    }
                    return each;
                }
            }
            alike.add(affine);
            scales.put(affine, new ArrayList<>(List.of(affine)));
            return affine;
        }
    }

    /**
     * A statement with every part a quantifier holds that is about no element it chose said outside
     * the quantifier — or nothing, where that is more than is said.
     *
     * <p>Such a part is the same thing of the same row whichever element the quantifier looks at,
     * so some element meeting what holds it is that part holding and some element meeting the rest
     * with it held, or the part failing and some element meeting the rest with it failing. Said that
     * way, the part is one part of what the quantifier stands in, beside the quantifier and the
     * others there, and the quantifiers left ask of their element alone. Read as a part of the
     * quantifier instead, the quantifier is one part and the part inside it is not, and where it
     * also stands outside, the two places are one part the statement cannot hold still at one and
     * move at the other.
     *
     * <p>A part about no element of an inner quantifier and about an element of an outer one is
     * said outside the inner one and inside the outer one, which is what it is about.
     *
     * <p>Said without taking cases where the statement lets it be: some element meeting one of
     * several things is some element meeting the first or some meeting another, and some element
     * meeting a part of the row and the rest is that part and some element meeting the rest. Only a
     * part of the row under a choice the element makes, as in {@code (p || e) && (q || f)}, is said
     * once held and once failing.
     *
     * <p>Each place a quantifier said writes out is a step against
     * {@link CompositionBudget#STEPS_A_STATEMENT_IS_READ_IN}: saying it is writing what it holds
     * again. A quantifier with several parts of the row under choices of what its element meets is
     * said once for every way they come out, which doubles with each of them.
     */
    private static final class Lifting {

        private int left = CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.maximum();

        /** {@code stated}, every quantifier in it said this way — itself where none has a part to
         *  say outside, and null where the steps ran out. */
        Proposition of(Proposition stated) {
            return switch (stated) {
                case Proposition.All all -> {
                    List<Proposition> parts = each(all.parts());
                    yield parts == null ? null
                            : parts == all.parts() ? stated : Proposition.all(parts);
                }
                case Proposition.Any any -> {
                    List<Proposition> parts = each(any.parts());
                    yield parts == null ? null
                            : parts == any.parts() ? stated : Proposition.any(parts);
                }
                case Proposition.Some some -> {
                    Proposition element = of(some.ofTheElement());
                    if (element == null) {
                        yield null;
                    }
                    if (element == some.ofTheElement()
                            && aboutNoElement(element, some.container()) == null) {
                        yield stated;
                    }
                    Proposition said = some(some.container(), element);
                    yield said == null ? null : some.holds() ? said : said.denied();
                }
                case Proposition.WhereItAnswers where -> {
                    Proposition answers = of(where.answers());
                    Proposition states = answers == null ? null : of(where.states());
                    yield states == null ? null
                            : answers == where.answers() && states == where.states() ? stated
                            : Proposition.whereItAnswers(answers, states);
                }
                case Proposition.SoManyHold counted -> {
                    List<Proposition> parts = each(counted.statements());
                    yield parts == null ? null : parts == counted.statements() ? stated
                            : Proposition.SoManyHold.counting(parts, counted.weights(),
                                    counted.admitted());
                }
                case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                     Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                     Proposition.LastToHold _, Proposition.Carried _, Proposition.SomeReachable _,
                     Proposition.Unread _, Proposition.OnAnApplication _ -> stated;
            };
        }

        /** Each of {@code parts} said this way — {@code parts} itself where none changed, and null
         *  where the steps ran out. */
        private List<Proposition> each(List<Proposition> parts) {
            List<Proposition> out = new ArrayList<>();
            boolean changed = false;
            for (Proposition part : parts) {
                Proposition said = of(part);
                if (said == null) {
                    return null;
                }
                changed |= said != part;
                out.add(said);
            }
            return changed ? out : parts;
        }

        /** Some element of {@code container} meeting {@code element}, with every part of
         *  {@code element} about no element of it said outside — {@code element} already said
         *  this way inside. */
        private Proposition some(DecisionSubject container, Proposition element) {
            long places = placesIn(element);
            if (places > left) {
                left = 0;
                return null;
            }
            left -= (int) places;
            return switch (element) {
                case Proposition.Always(boolean always) when !always -> element;
                case Proposition.Any any -> {
                    List<Proposition> each = new ArrayList<>();
                    for (Proposition one : any.parts()) {
                        Proposition said = some(container, one);
                        if (said == null) {
                            yield null;
                        }
                        each.add(said);
                    }
                    yield Proposition.any(each);
                }
                case Proposition.All all -> {
                    List<Proposition> ofTheRow = new ArrayList<>();
                    List<Proposition> rest = new ArrayList<>();
                    all.parts().forEach(part -> (part.mayTurnOnAnElementOf(container) ? rest
                            : ofTheRow).add(part));
                    if (ofTheRow.isEmpty()) {
                        yield eachWay(container, all);
                    }
                    Proposition said = some(container, Proposition.all(rest));
                    if (said == null) {
                        yield null;
                    }
                    ofTheRow.add(said);
                    yield Proposition.all(ofTheRow);
                }
                case Proposition.SoManyHold counted -> throw notWrittenOut(counted);
                // One part, about the element or not; what holds everywhere is about none, and
                // some element meeting it is the container holding one.
                case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                     Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                     Proposition.LastToHold _, Proposition.Some _, Proposition.Carried _,
                     Proposition.SomeReachable _, Proposition.Unread _,
                     Proposition.OnAnApplication _, Proposition.WhereItAnswers _ ->
                        element.mayTurnOnAnElementOf(container)
                        ? new Proposition.Some(container, element, true)
                        : Proposition.all(List.of(element, new Proposition.Some(container,
                                new Proposition.Always(true), true)));
            };
        }

        /**
         * Some element meeting {@code all}, every part of which may be about the element: said
         * once with the first part of the row inside it held, and once with it failing.
         *
         * <p>A conjunction holds no part that comes out one way for every row, since joining one
         * leaves it out ({@link Proposition#all}), so the part taken is one that is held and fails,
         * and each way leaves a statement without it.
         */
        private Proposition eachWay(DecisionSubject container, Proposition.All all) {
            Proposition row = aboutNoElement(all, container);
            if (row == null) {
                return new Proposition.Some(container, all, true);
            }
            Proposition held = some(container, with(all, row, true));
            if (held == null) {
                return null;
            }
            Proposition failing = some(container, with(all, row, false));
            if (failing == null) {
                return null;
            }
            return Proposition.any(List.of(Proposition.all(List.of(row, held)),
                    Proposition.all(List.of(row.denied(), failing))));
        }

        /** How many places a part stands at in {@code stated}, inside the quantifiers it holds as
         *  well: what saying a quantifier over it again writes out. */
        private static long placesIn(Proposition stated) {
            return switch (stated) {
                case Proposition.All all -> all.parts().stream().mapToLong(Lifting::placesIn).sum();
                case Proposition.Any any -> any.parts().stream().mapToLong(Lifting::placesIn).sum();
                case Proposition.Some some -> 1 + placesIn(some.ofTheElement());
                case Proposition.WhereItAnswers where ->
                        placesIn(where.answers()) + placesIn(where.states());
                case Proposition.SoManyHold counted -> throw notWrittenOut(counted);
                case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                     Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                     Proposition.LastToHold _, Proposition.Carried _, Proposition.SomeReachable _,
                     Proposition.Unread _, Proposition.OnAnApplication _ -> 1;
            };
        }

        /** The first part of {@code element}, held, about no element of {@code container}, or
         *  null where every part may be. */
        private static Proposition aboutNoElement(Proposition element,
                                                  DecisionSubject container) {
            Map<String, Proposition> parts = new TreeMap<>();
            gather(element, parts, new TreeMap<>());
            return parts.values().stream()
                    .filter(part -> !part.mayTurnOnAnElementOf(container))
                    .findFirst().orElse(null);
        }
    }

    /**
     * One statement read part against part: the parts it joins, each place one stands, and what it
     * comes to every way they can come out ({@link WhatAStatementComesTo}) — or not read, where
     * that took more steps than a statement is read in, or where the statement it stands in was
     * more than is lifted ({@link Lifting}).
     */
    private static final class Reading {

        private final Proposition stated;
        private final List<Proposition> named;
        private final Map<String, Integer> index;
        private final Map<String, Literal> leaves;
        /** Whether the statement was lifted, so that each part is one part of it. */
        private final boolean lifted;
        private final WhatAStatementComesTo ways;
        /** What the statement comes to, or {@link WhatAStatementComesTo#NOT_WORKED_OUT}. */
        private final int whole;
        /** Which ways the parts can come out together ({@link #canBe}), as a statement of
         *  {@link #ways}. */
        private final int possible;
        /** What every row meets of the parts, each a statement of its own ({@link #canBe}). */
        private final List<Proposition> canBe;
        /** The values the statement asks the case of more than once, which are what the statement
         *  is read under the cases of, and leave some ways out of {@link #canBe}. */
        private final List<AskedTwice> twice;
        /** Whether some part has asked for the statement under each case of a value. */
        private boolean readUnderEachCase;
        /** The statement under each case of a value, once some part asked for it — null where it
         *  asks no value's case twice. */
        private List<UnderACase> underEachCase;

        private Reading(Proposition stated, boolean lifted) {
            this.stated = stated;
            this.lifted = lifted;
            // In the order they first stand, which keeps the parts one conjunction or disjunction
            // joins next to each other: asked in that order, a statement of several such joined
            // together is left as few statements as it has joins, where asked with the parts of
            // each apart it is left as a different one for every way the earlier ones come out.
            Map<String, Proposition> parts = new LinkedHashMap<>();
            this.leaves = new TreeMap<>();
            gather(stated, parts, leaves);
            this.named = List.copyOf(parts.values());
            this.index = new TreeMap<>();
            for (int i = 0; i < named.size(); i++) {
                index.put(named.get(i).key(), i);
            }
            this.twice = askedTwice(named);
            this.ways = new WhatAStatementComesTo();
            this.canBe = lifted ? canBe(named, twice) : List.of();
            if (!lifted) {
                this.whole = WhatAStatementComesTo.NOT_WORKED_OUT;
                this.possible = WhatAStatementComesTo.NOT_WORKED_OUT;
                return;
            }
            WhatAStatementComesTo.Asking asking =
                    ways.asking(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.maximum());
            int comesTo = comesTo(stated, asking);
            int canBe = comesTo(Proposition.all(this.canBe), asking);
            boolean read = comesTo >= 0 && canBe >= 0;
            this.whole = read ? comesTo : WhatAStatementComesTo.NOT_WORKED_OUT;
            this.possible = read ? canBe : WhatAStatementComesTo.NOT_WORKED_OUT;
        }

        /** {@code stated} read, lifted. */
        static Reading of(Proposition stated) {
            return new Reading(stated, true);
        }

        /** {@code stated}, its parts named and nothing read of it. */
        static Reading unread(Proposition stated) {
            return new Reading(stated, false);
        }

        /** The parts the statement joins, held, in the order they first stand in it. */
        List<Proposition> named() {
            return named;
        }

        /** What {@code stated}, a statement of the parts, comes to as a statement of
         *  {@link #ways}, built by {@code asking}. */
        private int comesTo(Proposition stated, WhatAStatementComesTo.Asking asking) {
            return switch (stated) {
                case Proposition.All all -> {
                    int out = WhatAStatementComesTo.ALWAYS;
                    for (Proposition part : all.parts()) {
                        out = asking.both(out, comesTo(part, asking));
                    }
                    yield out;
                }
                case Proposition.Any any -> {
                    int out = WhatAStatementComesTo.NEVER;
                    for (Proposition part : any.parts()) {
                        out = asking.either(out, comesTo(part, asking));
                    }
                    yield out;
                }
                // Holding where it answers and states what it does; its denial is written as the
                // same answering with the statement denied, so this is that one too.
                case Proposition.WhereItAnswers where -> asking.both(
                        comesTo(where.answers(), asking), comesTo(where.states(), asking));
                case Proposition.Always(boolean holds) ->
                        holds ? WhatAStatementComesTo.ALWAYS : WhatAStatementComesTo.NEVER;
                case Proposition.SoManyHold counted -> comesToCounted(counted, asking);
                // A part, as it stands in the statement or as what every row meets of the parts
                // says it: held or denied, it is the part held, asked one way round.
                case Proposition.Compared _, Proposition.Truth _, Proposition.InCases _,
                     Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                     Proposition.Some _, Proposition.Carried _, Proposition.SomeReachable _,
                     Proposition.Unread _, Proposition.OnAnApplication _ -> {
                    Proposition held = held(stated);
                    yield asking.part(index.get(held.key()), held == stated);
                }
            };
        }

        /**
         * What a count of statements comes to as a statement of {@link #ways}: for each number
         * held so far, what the statements still to come make of it — held where the number is one
         * the count admits once they are all counted.
         *
         * <p>Built from the last statement to the first, one statement for each number a prefix of
         * the statements can come to, and not one for each set of statements that holds. Where the
         * statements are parts of their own, in the order they are asked, that is a statement for
         * each statement and number, however many sets of them come to the count.
         */
        private int comesToCounted(Proposition.SoManyHold counted,
                                   WhatAStatementComesTo.Asking asking) {
            List<Proposition> statements = counted.statements();
            int[] each = new int[statements.size()];
            for (int at = 0; at < each.length; at++) {
                each[at] = comesTo(statements.get(at), asking);
                if (each[at] < 0) {
                    return WhatAStatementComesTo.NOT_WORKED_OUT;
                }
            }
            int[] before = new int[each.length + 1];
            for (int at = 0; at < each.length; at++) {
                before[at + 1] = before[at] + counted.weights().get(at);
            }
            int[] coming = new int[before[each.length] + 1];
            for (int held = 0; held < coming.length; held++) {
                coming[held] = counted.admitted().contains(held) ? WhatAStatementComesTo.ALWAYS
                        : WhatAStatementComesTo.NEVER;
            }
            for (int at = each.length - 1; at >= 0; at--) {
                int[] here = new int[before[at] + 1];
                for (int held = 0; held < here.length; held++) {
                    int holding = coming[held + counted.weights().get(at)];
                    int failing = coming[held];
                    here[held] = asking.either(asking.both(each[at], holding),
                            asking.both(asking.not(each[at]), failing));
                    if (here[held] < 0) {
                        return WhatAStatementComesTo.NOT_WORKED_OUT;
                    }
                }
                coming = here;
            }
            return coming[0];
        }

        /**
         * Which ways the parts {@code named} can come out together, as statements of them every
         * row meets.
         *
         * <p>Said once and read twice: as what is possible when a line's cases are taken apart
         * ({@link #takenApart}), and as what a line said in one condition is said with
         * ({@link #whereItTurns}). Asked of each on its own, a way one of them knew no row is
         * would be one the other still read a line as deciding in.
         *
         * <p>Parts that say which cases one value of the input is are not free of each other: the
         * value is one case, so a way is one a row can be only where some one case is in every set
         * of cases held there and in none failing there. Kept in, a way where it is two at once is
         * a way where a line decides or does not, and what tells it from the rest is asked as a
         * part: {@code month.value <= minimum(term)} states its line at 12 where {@code term} is
         * {@code OneYear} and its line at 24 where it is {@code TwoYear}, and with a way where it
         * is both, the line at 12 decided only where the month is not above 24 as well.
         *
         * <p>The cases the parts name need not be every case of the value, so a value none of them
         * names is a case as well: every way holding none of them is possible.
         *
         * <p>Two quantifiers over one container are not free of each other either, where one asks
         * of its element everything the other asks and more
         * ({@link Proposition.Some.ElementAsked#holdsOnlyWhere}): no row holds an element meeting
         * the first and none meeting the second. {@code Map.get(k, m)} read with a default is
         * some entry under {@code k} whose value meets the comparison, or no entry under {@code k}
         * and the default meeting it. Kept in, the way with the first held and the second failing
         * is one where the default's comparison turns whether the entry's value is read, and the
         * entry's line is said in two cases told apart by a comparison of the default.
         *
         * <p>The way that leaves out has the stronger held, so every quantifier failing is a
         * possible way; and no quantifier holds only where another does with the other holding
         * only where it does, so in any possible way with some held, a held one that no other
         * held one holds only where it does can fail and leave a possible way. Every possible
         * way of the quantifiers is reached from all of them failing one at a time, which is what
         * lets a line's cases be told apart one part at a time ({@link #split}).
         *
         * <p>Two relations over one number are not taken in here, though {@code x > 5} holding
         * and {@code x > 0} failing is no row: whether rows on both sides of a line can be in a
         * case is asked of the rows, and said here it would be a part of every case the line is
         * read in.
         *
         * <p>The quantifiers compared are the parts of one statement, side by side: what stands
         * inside a quantifier or a search is not a part here, so two spelled over one container
         * are over one container.
         */
        private static List<Proposition> canBe(List<Proposition> named, List<AskedTwice> twice) {
            List<Proposition> out = new ArrayList<>();
            Map<DecisionSubject, List<Proposition.Some.ElementAsked>> byContainer =
                    new LinkedHashMap<>();
            for (Proposition part : named) {
                if (part instanceof Proposition.Some some) {
                    byContainer.computeIfAbsent(some.container(), _ -> new ArrayList<>())
                            .add(some.elementAsked());
                }
            }
            for (List<Proposition.Some.ElementAsked> overOne : byContainer.values()) {
                for (Proposition.Some.ElementAsked stronger : overOne) {
                    for (Proposition.Some.ElementAsked weaker : overOne) {
                        if (stronger.holdsOnlyWhere(weaker)) {
                            out.add(Proposition.any(List.of(stronger.quantifier().denied(),
                                    weaker.quantifier())));
                        }
                    }
                }
            }
            for (AskedTwice value : twice) {
                List<Integer> parts = value.parts();
                // Which of the parts hold for a value that is each case; and none of them for a
                // value that is a case none of them names.
                Set<Set<Integer>> holding = new LinkedHashSet<>();
                holding.add(Set.of());
                for (Refinement atom : value.atoms()) {
                    Set<Integer> those = new HashSet<>();
                    for (int each : parts) {
                        if (((Proposition.InCases) named.get(each)).cases().atoms()
                                .contains(atom)) {
                            those.add(each);
                        }
                    }
                    holding.add(those);
                }
                List<Proposition> ofTheValue = new ArrayList<>();
                for (Set<Integer> those : holding) {
                    ofTheValue.add(Proposition.all(parts.stream()
                            .map(each -> those.contains(each) ? named.get(each)
                                    : named.get(each).denied())
                            .toList()));
                }
                out.add(Proposition.any(ofTheValue));
            }
            return List.copyOf(out);
        }

        /**
         * Where {@code part} turns the statement, as cases.
         *
         * <p>Said one by one where the cases taken apart are as few as that. Where they are not —
         * more cases than are said one by one, no one part telling them apart, or more steps than
         * the statement is read in — the statement is read under each case of a value it asks the
         * case of, which leaves out the ways where the value is two cases as the taking apart
         * does.
         *
         * <p>Past both, where the line decides is said as one case, the statement with the line
         * held against the statement with it failing, standing for the cases it is said for: the
         * ones taken apart, as far as a line is taken apart into, or the ones read under each case
         * of a value — or, where neither came to the end, cases nobody took apart, naming the
         * figure that stopped it.
         */
        List<DecidingCase> turnsOn(Proposition part) {
            List<DecidingCase> byCount = lifted ? inEachCountOfTheOthers(part) : null;
            if (byCount != null) {
                return byCount;
            }
            // Taken apart once, as far as a line is: a case costs what tells it from the rest
            // and not a walk of every way, so a second taking apart past the first few would
            // only find those again.
            TakenApart taken = takenApart(part,
                    CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum());
            if (taken instanceof TakenApart.Taken(var cases) && cases.size() <= MOST_CASES) {
                return cases.stream().map(each -> DecidingCase.alone(Proposition.all(each)))
                        .toList();
            }
            if (lifted && !readUnderEachCase) {
                underEachCase = WhereEachLineDecides.underEachCase(stated, twice);
                readUnderEachCase = true;
            }
            List<DecidingCase> ofAValue = underEachCase == null ? null
                    : inEachCaseOfAValue(underEachCase, part);
            if (ofAValue != null && ofAValue.size() <= MOST_CASES) {
                return ofAValue;
            }
            Proposition said = whereItTurns(part);
            if (taken instanceof TakenApart.Taken(var cases)) {
                return List.of(new DecidingCase(said, DecidingCase.Cases.ofConjunctions(cases)));
            }
            if (ofAValue != null) {
                return List.of(new DecidingCase(said, DecidingCase.eachOf(ofAValue)));
            }
            return List.of(new DecidingCase(said, new DecidingCase.Cases.NotTakenApart(
                    switch (taken) {
                        case TakenApart.MoreThan _ ->
                                CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO;
                        case TakenApart.RanOut _ -> CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN;
                        // No one part tells the cases apart only where some ways are left out of
                        // what is possible, and only a value in twice leaves them out so: the
                        // statement is read under each case of the first of those. What else
                        // canBe leaves out joins any two possible ways by ways each one part apart
                        // from the last, every one of them possible, so where the line decides at
                        // one end and not at the other some part tells the two apart.
                        case TakenApart.ByNoOnePart _, TakenApart.Taken _ ->
                                throw new IllegalStateException("where " + part + " decides in "
                                        + stated + " was told apart by no one part, and the"
                                        + " statement asks no value's case twice");
                    })));
        }

        /**
         * Where {@code part} decides a count of statements, as a case for each number of the
         * others that holds — or null where the statement is not that.
         *
         * <p>The part stands in some statements of the count as it is and in some as its denial,
         * each written as many times as the count weighs it, and crossing its line moves every
         * one of those writings at once: the ones that are the part come to {@code held} more
         * where it holds, the ones that are its denial {@code denied} more where it fails. It
         * decides where the others come to a number {@code c} that the count admits at
         * {@code c + held} and not at {@code c + denied}, or the other way round — none at all
         * where the two weigh the same, as a value beside its denial does. A row on each side of
         * the line is in the same case only if the others come to the same number there. That is
         * one case for each such {@code c}, and not one for each set of the others that comes to
         * it: the sets are as many as the ways of choosing, and a number of them is a case.
         *
         * <p>Only where the others are free of each other and of the part ({@link #canBe} says
         * nothing of them) and none of them asks the part inside a statement of more than the
         * part, so that the others come to the same number on both sides of the line. And no more
         * cases than a line is said in; past them, the line is taken apart as any other.
         */
        private List<DecidingCase> inEachCountOfTheOthers(Proposition part) {
            if (!(stated instanceof Proposition.SoManyHold counted) || !canBe.isEmpty()) {
                return null;
            }
            int held = 0;
            int denied = 0;
            List<Proposition> others = new ArrayList<>();
            List<Integer> weighed = new ArrayList<>();
            for (int one = 0; one < counted.statements().size(); one++) {
                Proposition statement = counted.statements().get(one);
                int weight = counted.weights().get(one);
                if (!(statement instanceof Proposition.All || statement instanceof Proposition.Any
                        || statement instanceof Proposition.WhereItAnswers
                        || statement instanceof Proposition.SoManyHold)
                        && held(statement).key().equals(part.key())) {
                    if (statement.key().equals(part.key())) {
                        held += weight;
                    } else {
                        denied += weight;
                    }
                    continue;
                }
                Map<String, Proposition> asked = new TreeMap<>();
                gather(statement, asked, new TreeMap<>());
                if (asked.containsKey(part.key())) {
                    return null;
                }
                others.add(statement);
                weighed.add(weight);
            }
            if (held + denied == 0) {
                return null;
            }
            int most = counted.weight() - held - denied;
            List<DecidingCase> out = new ArrayList<>();
            for (int count = 0; count <= most; count++) {
                if (counted.admitted().contains(count + held)
                        != counted.admitted().contains(count + denied)) {
                    out.add(DecidingCase.alone(Proposition.SoManyHold.counting(others, weighed,
                            List.of(count))));
                }
            }
            return out.size() <= MOST_CASES ? out : null;
        }

        /**
         * Where {@code part} turns the statement, said in one condition: the statement with it
         * held against the statement with it failing, where it can come out either way. Of what
         * every row meets ({@link #canBe}), the parts that ask {@code part} are said with it held
         * and with it failing; the rest hold of every row whichever way it comes out, and say
         * nothing of where it turns.
         */
        private Proposition whereItTurns(Proposition part) {
            List<Proposition> parts = new ArrayList<>();
            parts.add(heldAgainstItsDenial(stated, part));
            for (Proposition each : canBe) {
                Proposition held = with(each, part, true);
                Proposition failing = with(each, part, false);
                if (!held.key().equals(each.key()) || !failing.key().equals(each.key())) {
                    parts.add(held);
                    parts.add(failing);
                }
            }
            return Proposition.all(parts);
        }

        /**
         * Where {@code part} decides, taken apart into {@code most} cases at most.
         *
         * <p>Only at a way of the other parts where {@code part} can come out either way: where
         * one of the two is no row's, nothing turns {@code part} there, and the statement coming
         * out differently with it held and failing is no case where it decides. The cases are then
         * over the other parts, and so is what is possible of them.
         */
        private TakenApart takenApart(Proposition part, int most) {
            if (whole < 0) {
                return new TakenApart.RanOut();
            }
            WhatAStatementComesTo.Asking asking =
                    ways.asking(CompositionBudget.STEPS_A_STATEMENT_IS_READ_IN.maximum());
            int at = index.get(part.key());
            int held = asking.with(possible, at, true);
            int failing = asking.with(possible, at, false);
            int decides = asking.both(asking.oneNotTheOther(asking.with(whole, at, true),
                    asking.with(whole, at, false)), asking.both(held, failing));
            List<List<Proposition>> cases = new ArrayList<>();
            return switch (split(asking, decides, asking.either(held, failing), new ArrayList<>(),
                    most, cases)) {
                case NOT -> new TakenApart.Taken(cases);
                case PAST_THE_FIGURE -> new TakenApart.MoreThan();
                case BY_NO_ONE_PART -> new TakenApart.ByNoOnePart();
                case OUT_OF_STEPS -> new TakenApart.RanOut();
            };
        }

        /**
         * The cases under {@code asked}, {@code decides} and {@code possible} said with the parts
         * in it come out as it says them — stopped as soon as
         * there are more than {@code most}, so the limit bounds the work and not only what is
         * kept.
         *
         * <p>The line decides at a way its other parts come out where the statement comes out
         * differently with the line held and with it failing. The cases are taken by asking the
         * other parts one at a time, in order, each only where what is left still turns on it: a
         * part every way left decides under, or none does, says nothing more. Asked only of the
         * ways the parts can come out together: what a way no row is comes to says nothing about
         * where a row has to be.
         *
         * <p>Stopped as well where no one part tells the ways the line decides at from the rest.
         * Every way being possible, some part always does; with ways no row is left out, the two
         * may be apart in two parts at once, and the cases are not said this way.
         */
        private Stopped split(WhatAStatementComesTo.Asking asking, int decides, int possible,
                              List<Proposition> asked, int most, List<List<Proposition>> into) {
            int some = asking.both(decides, possible);
            int notEvery = asking.both(asking.not(decides), possible);
            if (some < 0 || notEvery < 0) {
                return Stopped.OUT_OF_STEPS;
            }
            if (some == WhatAStatementComesTo.NEVER) {
                return Stopped.NOT;
            }
            if (notEvery == WhatAStatementComesTo.NEVER) {
                into.add(List.copyOf(asked));
                return into.size() <= most ? Stopped.NOT : Stopped.PAST_THE_FIGURE;
            }
            // Only the parts where the line decides still asks: a part it does not ask turns
            // nothing of it, and a part asked before and the line are none of them. With every
            // way possible, the first it asks turns it, since it is held only where it does.
            BitSet parts = possible == WhatAStatementComesTo.ALWAYS
                    ? ways.firstPartAsked(decides) : ways.partsAsked(decides);
            for (int part = parts.nextSetBit(0); part >= 0; part = parts.nextSetBit(part + 1)) {
                int turns = splitsOn(asking, decides, possible, part);
                if (turns < 0) {
                    return Stopped.OUT_OF_STEPS;
                }
                if (turns == WhatAStatementComesTo.NEVER) {
                    continue;
                }
                List<Proposition> held = new ArrayList<>(asked);
                held.add(named.get(part));
                Stopped holding = split(asking, asking.with(decides, part, true),
                        asking.with(possible, part, true), held, most, into);
                if (holding != Stopped.NOT) {
                    return holding;
                }
                List<Proposition> failing = new ArrayList<>(asked);
                failing.add(named.get(part).denied());
                return split(asking, asking.with(decides, part, false),
                        asking.with(possible, part, false), failing, most, into);
            }
            return Stopped.BY_NO_ONE_PART;
        }

        /** Where, between two ways both possible that differ in {@code part} alone, whether the
         *  line decides differs: {@link WhatAStatementComesTo#NEVER} where nowhere. */
        private static int splitsOn(WhatAStatementComesTo.Asking asking, int decides,
                                    int possible, int part) {
            return asking.both(
                    asking.both(asking.with(possible, part, false),
                            asking.with(possible, part, true)),
                    asking.oneNotTheOther(asking.with(decides, part, false),
                            asking.with(decides, part, true)));
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
            case Proposition.WhereItAnswers where -> statesARelation(where.states());
            case Proposition.SoManyHold counted -> counted.statements().stream()
                    .anyMatch(WhereEachLineDecides::statesARelation);
            case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                 Proposition.Some _, Proposition.Carried _, Proposition.SomeReachable _,
                 Proposition.Unread _, Proposition.OnAnApplication _ -> false;
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
            case Proposition.WhereItAnswers where -> {
                gather(where.answers(), parts, leaves);
                gather(where.states(), parts, leaves);
            }
            case Proposition.SoManyHold counted ->
                    counted.statements().forEach(part -> gather(part, parts, leaves));
            case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                 Proposition.LastToHold _, Proposition.Some _, Proposition.Carried _,
                 Proposition.SomeReachable _, Proposition.Unread _,
                 Proposition.OnAnApplication _ -> {
                Proposition held = held(stated);
                parts.putIfAbsent(held.key(), held);
                leaves.putIfAbsent(stated.key(), new Literal(held.key(), held == stated));
            }
        }
    }

    /**
     * The parts of {@code stated}, held, that stand nowhere but in where a part of it answers
     * ({@link Proposition.WhereItAnswers#answers}). None of them is a line: a row where one fails is
     * a row the statement says nothing of, so it stands on no side of anything, and what such a
     * part does is narrow the cases the lines of the rest decide in.
     */
    private static Set<String> onlyWhereItAnswers(Proposition stated) {
        Map<String, Proposition> answering = new TreeMap<>();
        Map<String, Proposition> stating = new TreeMap<>();
        partsBy(stated, false, answering, stating);
        Set<String> out = new HashSet<>(answering.keySet());
        out.removeAll(stating.keySet());
        return out;
    }

    /** Every part {@code stated} joins, held, filed by whether it stands in where it answers. */
    private static void partsBy(Proposition stated, boolean answering,
                                Map<String, Proposition> where, Map<String, Proposition> what) {
        switch (stated) {
            case Proposition.All all ->
                    all.parts().forEach(part -> partsBy(part, answering, where, what));
            case Proposition.Any any ->
                    any.parts().forEach(part -> partsBy(part, answering, where, what));
            case Proposition.WhereItAnswers inside -> {
                partsBy(inside.answers(), true, where, what);
                partsBy(inside.states(), answering, where, what);
            }
            case Proposition.SoManyHold counted ->
                    counted.statements().forEach(part -> partsBy(part, answering, where, what));
            case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                 Proposition.LastToHold _, Proposition.Some _, Proposition.Carried _,
                 Proposition.SomeReachable _, Proposition.Unread _,
                 Proposition.OnAnApplication _ -> {
                Proposition held = held(stated);
                (answering ? where : what).putIfAbsent(held.key(), held);
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
            case Proposition.SoManyHold counted -> throw notWrittenOut(counted);
            case Proposition.All _, Proposition.Any _, Proposition.WhereItAnswers _ ->
                    throw new IllegalArgumentException(
                            "a part is what a conjunction or a disjunction joins: " + part);
        };
        return holds ? part : part.denied();
    }

    /**
     * Where a line decides, taken apart: the cases, each the parts it asks; more than were taken
     * apart; no one part telling them apart; or more steps than a statement is read in.
     *
     * <p>Four answers and not a list that is sometimes long and sometimes absent. More cases than a
     * figure lets be taken apart and more steps than another lets be taken are stops at two
     * figures, and ways that no one part tells apart are something about the statement; told
     * apart by how many cases came back, they were one reading's guess about another.
     */
    private sealed interface TakenApart {

        /** The cases, each the parts it asks. */
        record Taken(List<List<Proposition>> cases) implements TakenApart {

            public Taken {
                cases = List.copyOf(cases);
            }
        }

        /** More cases than were taken apart. */
        record MoreThan() implements TakenApart {}

        /** No one part tells where the line decides from the rest ({@link Reading#split}). */
        record ByNoOnePart() implements TakenApart {}

        /** More steps than a statement is read in
         *  ({@link CompositionBudget#STEPS_A_STATEMENT_IS_READ_IN}). */
        record RanOut() implements TakenApart {}
    }

    /** How a taking apart ({@link Reading#split}) stopped, where it did not come to the end. */
    private enum Stopped {
        /** At the end, every case taken. */
        NOT,
        /** One case past the figure. */
        PAST_THE_FIGURE,
        /** Where no one part tells the ways the line decides at from the rest. */
        BY_NO_ONE_PART,
        /** Out of steps. */
        OUT_OF_STEPS
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
     * Where {@code part} decides in a statement whose cases taking apart does not say, read in each
     * case of one value the statement asks the case of, which may be more cases than are said one
     * by one.
     *
     * <p>The cases of one value are never two at once, and a statement whose cases are more than
     * are said one by one, or that no one part tells apart, or that took more steps than are
     * taken, is read under each case of the value instead: every part asking which case it is
     * comes out one way, and what is left is a statement of the parts that case has. {@code days <= limit(s)} with {@code limit} choosing one of eight numbers is,
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
     * A value of the row a statement asks the case of more than once: the parts that ask it, by
     * where they stand among the statement's parts, and every case they name.
     *
     * <p>One answer for the two things that turn on it. Those parts are not free of each other
     * ({@link Reading#canBe}), and so where the line decides may be told apart by no one part;
     * read under each case of the value instead ({@link #underEachCase}), they come out one way
     * each. Each asking which values those are on its own, the second answer was the first's only
     * by both being written alike.
     */
    private record AskedTwice(DecisionSubject value, List<Integer> parts, List<Refinement> atoms) {}

    /** Every value of the row {@code named} asks the case of more than once, in the order they are
     *  first asked. */
    private static List<AskedTwice> askedTwice(List<Proposition> named) {
        Map<DecisionSubject, List<Integer>> byValue = new LinkedHashMap<>();
        for (int i = 0; i < named.size(); i++) {
            if (named.get(i) instanceof Proposition.InCases cases && oneValueOfTheRow(cases)) {
                byValue.computeIfAbsent(cases.of(), _ -> new ArrayList<>()).add(i);
            }
        }
        List<AskedTwice> out = new ArrayList<>();
        byValue.forEach((value, parts) -> {
            if (parts.size() < 2) {
                return;
            }
            List<Refinement> atoms = new ArrayList<>();
            for (int each : parts) {
                ((Proposition.InCases) named.get(each)).cases().atoms().stream()
                        .filter(atom -> !atoms.contains(atom)).forEach(atoms::add);
            }
            out.add(new AskedTwice(value, List.copyOf(parts), List.copyOf(atoms)));
        });
        return List.copyOf(out);
    }

    /**
     * {@code stated} read under each case of the first value it asks the case of more than once,
     * and under that value being none of them — or null where it asks no value's case twice.
     *
     * <p>The same for every part of the statement, so worked out once for the statement and asked
     * of by each of its parts. A value inside the elements or the keys of a container is not one
     * value of the row, and is not read this way.
     *
     * @param twice the values {@code stated} asks the case of more than once ({@link #askedTwice})
     */
    private static List<UnderACase> underEachCase(Proposition stated, List<AskedTwice> twice) {
        if (twice.isEmpty()) {
            return null;
        }
        DecisionSubject value = twice.getFirst().value();
        List<Refinement> atoms = twice.getFirst().atoms();
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
     * <p>A case taken apart says the parts asked before it failing beside the one that
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
            case Proposition.WhereItAnswers where -> Proposition.whereItAnswers(
                    assuming(where.answers(), value, atoms),
                    assuming(where.states(), value, atoms));
            case Proposition.InCases cases when cases.of().equals(value) -> new Proposition.Always(
                    atoms.stream().anyMatch(cases.cases().atoms()::contains) == cases.holds());
            case Proposition.Some some -> new Proposition.Some(some.container(),
                    assuming(some.ofTheElement(), value, atoms), some.holds());
            case Proposition.SoManyHold counted ->
                    counted.mapped(each -> assuming(each, value, atoms));
            case Proposition.InCases _, Proposition.Always _, Proposition.Compared _,
                 Proposition.Truth _, Proposition.Present _, Proposition.SameValue _,
                 Proposition.LastToHold _, Proposition.Carried _, Proposition.SomeReachable _,
                 Proposition.Unread _, Proposition.OnAnApplication _ -> stated;
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
            case Proposition.WhereItAnswers where -> Proposition.whereItAnswers(
                    with(where.answers(), part, holds), with(where.states(), part, holds));
            case Proposition.SoManyHold counted ->
                    counted.mapped(each -> with(each, part, holds));
            case Proposition leaf when standsAs(leaf, part) ->
                    new Proposition.Always(leaf.key().equals(part.key()) == holds);
            case Proposition.Some some when !part.mayTurnOnAnElementOf(some.container()) ->
                    new Proposition.Some(some.container(), with(some.ofTheElement(), part, holds),
                            some.holds());
            case Proposition.Some _, Proposition.Always _, Proposition.Compared _,
                 Proposition.Truth _, Proposition.InCases _, Proposition.Present _,
                 Proposition.SameValue _, Proposition.LastToHold _, Proposition.Carried _,
                 Proposition.SomeReachable _, Proposition.Unread _,
                 Proposition.OnAnApplication _ -> stated;
        };
    }

    /**
     * What is thrown where a count of statements reaches a reader here, which none does: a
     * statement is handed here with every count in it written out as its choices
     * ({@link CountsWrittenOut}), inside what a search reaches as well.
     */
    private static IllegalArgumentException notWrittenOut(Proposition.SoManyHold counted) {
        return new IllegalArgumentException(
                "a count reaches this reader written out as its choices: " + counted);
    }
}
