package souther.compiler.proof;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.SideAnswered;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * Whether statements about values follow from others: whether no way for the values to be makes
 * every one of the others hold and the statement fail.
 *
 * <p>Searched for, and not decided by a rule about any operation. The statements are split into the
 * ways they can hold — a disjunction into its parts — and each way is a set of truths about atoms
 * (that a value holds something, that some element meets something) and of comparisons between
 * numbers of them. A way is ruled out where two of its truths disagree or its comparisons leave no
 * number anywhere ({@link NumericDomain}). The statement follows where every way is ruled out.
 *
 * <p>What is known of atoms whatever made them is put in beside them, and only that: a size is no
 * less than nought, a value holds something exactly where its size is at least one, a count of the
 * elements meeting something is no less than nought and no more than there are, and some element
 * meets it exactly where the count is at least one.
 *
 * <p>Sound and short of complete: a comparison the numeric domain cannot rule out leaves a way
 * open, and a way left open is a statement not shown to follow — never one shown to follow that
 * does not.
 */
final class Validity {

    /** How many ways a search may open before it gives up and says nothing follows. */
    private static final int WAYS = 200_000;

    /** How deep a question about what an element meets is asked inside another. */
    private static final int DEEPEST = 2;

    private final Function<Value, Granularity> spacing;
    private final int depth;
    private final Map<LawNumber<Value>, Integer> numbers = new LinkedHashMap<>();
    private int ways;

    private Validity(Function<Value, Granularity> spacing, int depth) {
        this.spacing = spacing;
        this.depth = depth;
    }

    /**
     * Whether {@code goal} holds wherever every one of {@code given} does.
     *
     * @param spacing how the values a number of a value can be are spaced, for the numbers that
     *                are a value itself rather than a size or a count
     */
    static boolean follows(List<LawProposition<Value>> given, LawProposition<Value> goal,
                           Function<Value, Granularity> spacing) {
        Validity search = new Validity(spacing, 0);
        Deque<LawProposition<Value>> todo = new ArrayDeque<>(given);
        todo.add(goal.denied());
        return !search.holdsSomewhere(todo, new ArrayList<>(), new HashMap<>(),
                NumericDomain.top(Integer::compare),
                new HashSet<>());
    }

    /** A truth about an atom, keyed by what it is about. */
    private sealed interface Atom {

        /** That a value comes out on the holding side of an aspect. */
        record Holds(Value value, AnswerAspect aspect) implements Atom {}

        /** That some element of a container meets a statement about it. */
        record Some(Value container, LawProposition<Value> ofTheElement) implements Atom {}

        /** That two values are one. */
        record Alike(Set<Value> values) implements Atom {}
    }

    /**
     * Whether some way of {@code todo} holding is left, with {@code waiting} the disjunctions met
     * and not yet split, {@code truths} already taken as they are, {@code where} the comparisons
     * taken so far leave the numbers, and {@code known} the atoms whose standing truths are already
     * among the work.
     *
     * <p>Every truth that is no choice is taken before any disjunction is split: a part of one that
     * the truths taken already settle is dropped or settles it, one with a single part left is that
     * part, and only where none is left like that is one split — the one with fewest parts.
     */
    private boolean holdsSomewhere(Deque<LawProposition<Value>> todo,
                                   List<List<LawProposition<Value>>> waiting,
                                   Map<Atom, Boolean> truths, NumericDomain<Integer> where,
                                   Set<Object> known) {
        if (++ways > WAYS) {
            return true;   // gave up: nothing is shown to follow
        }
        while (true) {
            while (!todo.isEmpty()) {
                LawProposition<Value> next = todo.pop();
                switch (next) {
                    case LawProposition.Always<Value>(boolean holds) -> {
                        if (!holds) {
                            return false;
                        }
                    }
                    case LawProposition.All<Value>(List<LawProposition<Value>> parts) ->
                            parts.reversed().forEach(todo::push);
                    case LawProposition.Any<Value>(List<LawProposition<Value>> parts) ->
                            waiting.add(parts);
                    case LawProposition.Compared<Value>(LinearForm<LawNumber<Value>> form,
                                                        Rel states) -> {
                        if (states == Rel.NE) {
                            todo.push(Props.either(new LawProposition.Compared<>(form, Rel.LT),
                                    new LawProposition.Compared<>(form, Rel.GT)));
                            continue;
                        }
                        for (LawNumber<Value> number : form.coefs().keySet()) {
                            if (known.add(number)) {
                                standing(number).forEach(todo::push);
                                countsBetween(number, known, todo);
                                numberCongruent(number, truths, known, todo);
                            }
                        }
                        where = where.assume(numbered(form), states, spacings(form));
                        if (where.isBottom()) {
                            return false;
                        }
                    }
                    case LawProposition.Observed<Value>(LawSubject<Value> of,
                                                        SideAnswered side) -> {
                        Atom atom = new Atom.Holds(valueOf(of), side.aspect());
                        if (!take(atom, side.holds(), truths, todo, known)) {
                            return false;
                        }
                    }
                    case LawProposition.SomeElement<Value>(Value container,
                                                           LawProposition<Value> ofTheElement,
                                                           boolean holds) -> {
                        if (!take(new Atom.Some(container, ofTheElement), holds, truths, todo,
                                known)) {
                            return false;
                        }
                    }
                    case LawProposition.Same<Value>(LawSubject<Value> one, LawSubject<Value> other,
                                                    boolean holds) -> {
                        Value a = valueOf(one);
                        Value b = valueOf(other);
                        if (a.equals(b)) {
                            if (!holds) {
                                return false;
                            }
                            continue;
                        }
                        if (!take(new Atom.Alike(Set.of(a, b)), holds, truths, todo, known)) {
                            return false;
                        }
                    }
                }
            }
            List<List<LawProposition<Value>>> still = new ArrayList<>();
            for (List<LawProposition<Value>> parts : waiting) {
                List<LawProposition<Value>> open = new ArrayList<>();
                boolean met = false;
                for (LawProposition<Value> part : parts) {
                    Boolean settled = settled(part, truths, where);
                    if (Boolean.TRUE.equals(settled)) {
                        met = true;
                        break;
                    }
                    if (settled == null) {
                        open.add(part);
                    }
                }
                if (met) {
                    continue;
                }
                if (open.isEmpty()) {
                    return false;
                }
                if (open.size() == 1) {
                    todo.push(open.get(0));
                } else {
                    still.add(open);
                }
            }
            waiting = still;
            if (!todo.isEmpty()) {
                continue;
            }
            if (waiting.isEmpty()) {
                return true;
            }
            List<LawProposition<Value>> split = waiting.get(0);
            for (List<LawProposition<Value>> each : waiting) {
                if (each.size() < split.size()) {
                    split = each;
                }
            }
            List<List<LawProposition<Value>>> rest = new ArrayList<>(waiting);
            rest.remove(split);
            for (LawProposition<Value> part : split) {
                Deque<LawProposition<Value>> branch = new ArrayDeque<>();
                branch.push(part);
                if (holdsSomewhere(branch, new ArrayList<>(rest), new HashMap<>(truths), where,
                        new HashSet<>(known))) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * Whether {@code part} is already settled by {@code truths} and {@code where} — true, false, or
     * null where it is not.
     */
    private Boolean settled(LawProposition<Value> part, Map<Atom, Boolean> truths,
                            NumericDomain<Integer> where) {
        return switch (part) {
            case LawProposition.Always<Value>(boolean holds) -> holds;
            case LawProposition.Observed<Value>(LawSubject<Value> of, SideAnswered side) ->
                    polarity(truths.get(new Atom.Holds(valueOf(of), side.aspect())), side.holds());
            case LawProposition.SomeElement<Value>(Value container, var ofTheElement,
                                                   boolean holds) ->
                    polarity(truths.get(new Atom.Some(container, ofTheElement)), holds);
            case LawProposition.Same<Value>(LawSubject<Value> one, LawSubject<Value> other,
                                            boolean holds) -> {
                Value a = valueOf(one);
                Value b = valueOf(other);
                yield a.equals(b) ? Boolean.valueOf(holds)
                        : polarity(truths.get(new Atom.Alike(Set.of(a, b))), holds);
            }
            case LawProposition.Compared<Value>(LinearForm<LawNumber<Value>> form, Rel states) -> {
                if (!numbers.keySet().containsAll(form.coefs().keySet())) {
                    yield null;   // a number nothing has said anything of yet settles nothing
                }
                LinearForm<Integer> read = numbered(form);
                yield where.entails(read, states) ? Boolean.TRUE
                        : where.refutes(read, states) ? Boolean.FALSE : null;
            }
            case LawProposition.All<Value>(var parts) -> {
                boolean all = true;
                for (LawProposition<Value> each : parts) {
                    Boolean one = settled(each, truths, where);
                    if (Boolean.FALSE.equals(one)) {
                        yield false;
                    }
                    all &= Boolean.TRUE.equals(one);
                }
                yield all ? Boolean.TRUE : null;
            }
            case LawProposition.Any<Value>(var parts) -> {
                boolean none = true;
                for (LawProposition<Value> each : parts) {
                    Boolean one = settled(each, truths, where);
                    if (Boolean.TRUE.equals(one)) {
                        yield true;
                    }
                    none &= Boolean.FALSE.equals(one);
                }
                yield none ? Boolean.FALSE : null;
            }
        };
    }

    /** {@code truth}, an atom's, as a statement of it taken {@code holds} comes out. */
    private static Boolean polarity(Boolean truth, boolean holds) {
        return truth == null ? null : truth == holds;
    }

    /** Takes {@code atom} as {@code holds}, answering false where that disagrees with a truth
     *  already taken. */
    private boolean take(Atom atom, boolean holds, Map<Atom, Boolean> truths,
                         Deque<LawProposition<Value>> todo, Set<Object> known) {
        Boolean already = truths.putIfAbsent(atom, holds);
        if (already != null) {
            return already == holds;
        }
        if (known.add(atom)) {
            standing(atom).forEach(todo::push);
            if (atom instanceof Atom.Some some) {
                for (Object other : List.copyOf(known)) {
                    if (other instanceof Atom.Some them && them.container().equals(some.container())
                            && !them.equals(some)) {
                        between(some, them).forEach(todo::push);
                    }
                }
            }
        }
        congruent(atom, holds, truths, known, todo);
        return true;
    }

    /**
     * What two values being one says of the truths and numbers taken: two of them that are one
     * once the one value is put in place of the other are one. Asked where two values are taken to
     * be one, of every two truths and every two numbers already taken; and where a truth or a
     * number is taken, of it and each already taken, under every two values already taken to be
     * one.
     *
     * <p>Between what is taken and nothing else. A truth about something made of the one value is
     * not made up for the other where nothing asked about it, so this adds no atom to the search.
     * And not where one of the two values is made of the other, since putting it in place of the
     * other changes what it is put in.
     */
    private static void congruent(Atom atom, boolean holds, Map<Atom, Boolean> truths,
                                  Set<Object> known, Deque<LawProposition<Value>> todo) {
        if (atom instanceof Atom.Alike(Set<Value> values)) {
            if (!holds) {
                return;
            }
            List<Value> two = List.copyOf(values);
            if (inside(two.get(0), two.get(1)) || inside(two.get(1), two.get(0))) {
                return;
            }
            Map<LawProposition<Value>, LawProposition<Value>> byImage = new HashMap<>();
            for (Atom taken : List.copyOf(truths.keySet())) {
                if (!taken.equals(atom)) {
                    LawProposition<Value> statement = statementOf(taken);
                    LawProposition<Value> first = byImage.putIfAbsent(
                            Substituted.proposition(statement, two.get(0), two.get(1)), statement);
                    if (first != null) {
                        todo.push(Props.same(first, statement));
                    }
                }
            }
            Map<LawNumber<Value>, LawNumber<Value>> numbersByImage = new HashMap<>();
            for (LawNumber<Value> number : numbersIn(known)) {
                LawNumber<Value> first = numbersByImage.putIfAbsent(
                        Substituted.number(number, two.get(0), two.get(1)), number);
                if (first != null) {
                    todo.push(equal(first, number));
                }
            }
            return;
        }
        LawProposition<Value> statement = statementOf(atom);
        for (List<Value> two : alike(truths)) {
            LawProposition<Value> image =
                    Substituted.proposition(statement, two.get(0), two.get(1));
            for (Atom taken : List.copyOf(truths.keySet())) {
                if (!taken.equals(atom) && !(taken instanceof Atom.Alike)) {
                    LawProposition<Value> other = statementOf(taken);
                    if (image.equals(Substituted.proposition(other, two.get(0), two.get(1)))) {
                        todo.push(Props.same(statement, other));
                    }
                }
            }
        }
    }

    /** What every two values already taken to be one say of {@code number}, just taken, and each
     *  number taken before it. */
    private static void numberCongruent(LawNumber<Value> number, Map<Atom, Boolean> truths,
                                        Set<Object> known, Deque<LawProposition<Value>> todo) {
        for (List<Value> two : alike(truths)) {
            LawNumber<Value> image = Substituted.number(number, two.get(0), two.get(1));
            for (LawNumber<Value> other : numbersIn(known)) {
                if (!other.equals(number)
                        && image.equals(Substituted.number(other, two.get(0), two.get(1)))) {
                    todo.push(equal(number, other));
                }
            }
        }
    }

    /** Every two values taken to be one, where neither is made of the other. */
    private static List<List<Value>> alike(Map<Atom, Boolean> truths) {
        List<List<Value>> out = new ArrayList<>();
        truths.forEach((atom, holds) -> {
            if (holds && atom instanceof Atom.Alike(Set<Value> values)) {
                List<Value> two = List.copyOf(values);
                if (!inside(two.get(0), two.get(1)) && !inside(two.get(1), two.get(0))) {
                    out.add(two);
                }
            }
        });
        return out;
    }

    @SuppressWarnings("unchecked")
    private static List<LawNumber<Value>> numbersIn(Set<Object> known) {
        List<LawNumber<Value>> out = new ArrayList<>();
        for (Object each : known) {
            if (each instanceof LawNumber<?> number) {
                out.add((LawNumber<Value>) number);
            }
        }
        return out;
    }

    private static LawProposition<Value> equal(LawNumber<Value> one, LawNumber<Value> other) {
        return Props.compared(Props.minus(LinearForm.atom(one), LinearForm.atom(other)), Rel.EQ);
    }

    /** Whether {@code part} stands somewhere inside {@code whole}, other than as all of it. */
    private static boolean inside(Value part, Value whole) {
        return !part.equals(whole) && !Substituted.value(whole, part, new Value.NothingYet())
                .equals(whole);
    }

    /** The statement that {@code atom} holds. */
    private static LawProposition<Value> statementOf(Atom atom) {
        return switch (atom) {
            case Atom.Holds(Value value, AnswerAspect aspect) -> new LawProposition.Observed<>(
                    new LawSubject.Argument<>(value), new SideAnswered(aspect, true));
            case Atom.Some(Value container, LawProposition<Value> ofTheElement) ->
                    new LawProposition.SomeElement<>(container, ofTheElement, true);
            case Atom.Alike(Set<Value> values) -> {
                List<Value> two = List.copyOf(values);
                yield new LawProposition.Same<>(new LawSubject.Argument<>(two.get(0)),
                        new LawSubject.Argument<>(two.get(1)), true);
            }
        };
    }

    /**
     * What one statement about some element of a container says of another about the same
     * container: where what the one says of an element is enough for the other's, that some element
     * meets the one is enough for some element meeting the other.
     */
    private List<LawProposition<Value>> between(Atom.Some one, Atom.Some other) {
        List<LawProposition<Value>> out = new ArrayList<>();
        if (enough(one.ofTheElement(), other.ofTheElement())) {
            out.add(Props.either(new LawProposition.SomeElement<>(one.container(),
                    one.ofTheElement(), false), new LawProposition.SomeElement<>(
                    other.container(), other.ofTheElement(), true)));
        }
        if (enough(other.ofTheElement(), one.ofTheElement())) {
            out.add(Props.either(new LawProposition.SomeElement<>(other.container(),
                    other.ofTheElement(), false), new LawProposition.SomeElement<>(
                    one.container(), one.ofTheElement(), true)));
        }
        return out;
    }

    /**
     * The same of the counts, where {@code number} is a count just taken: of each count of the same
     * container already taken, where what one says of an element is enough for the other's, the
     * one counts no more than the other.
     *
     * <p>Asked of counts and not of every statement that some element meets something, since a
     * count is a number the search has to carry and a statement nothing counts is not.
     */
    private void countsBetween(LawNumber<Value> number, Set<Object> known,
                               Deque<LawProposition<Value>> todo) {
        if (!(number instanceof LawNumber.HowManyMeet<Value>(Value container,
                LawProposition<Value> ofTheElement))
                || container instanceof Value.Listed) {
            return;
        }
        for (LawNumber<Value> other : numbersIn(known)) {
            if (other instanceof LawNumber.HowManyMeet<Value>(Value them, var theirs)
                    && them.equals(container) && !other.equals(number)) {
                if (enough(ofTheElement, theirs)) {
                    todo.push(Props.compared(Props.minus(LinearForm.atom(other),
                            LinearForm.atom(number)), Rel.GE));
                }
                if (enough(theirs, ofTheElement)) {
                    todo.push(Props.compared(Props.minus(LinearForm.atom(number),
                            LinearForm.atom(other)), Rel.GE));
                }
            }
        }
    }

    /** Whether {@code one}, said of an element, is enough for {@code other} said of it. */
    private boolean enough(LawProposition<Value> one, LawProposition<Value> other) {
        return depth < DEEPEST && new Validity(spacing, depth + 1).holdsNowhere(one, other);
    }

    /** Whether no way has {@code one} hold and {@code other} fail. */
    private boolean holdsNowhere(LawProposition<Value> one, LawProposition<Value> other) {
        Deque<LawProposition<Value>> todo = new ArrayDeque<>(List.of(one, other.denied()));
        return !holdsSomewhere(todo, new ArrayList<>(), new HashMap<>(),
                NumericDomain.top(Integer::compare),
                new HashSet<>());
    }

    private static Value valueOf(LawSubject<Value> subject) {
        if (!(subject instanceof LawSubject.Argument<Value>(Value value))) {
            throw new IllegalArgumentException("a statement here is about values and names none"
                    + " by its place: " + subject);
        }
        return value;
    }

    // --- what is known of an atom whatever made it ----------------------------------------------

    private static List<LawProposition<Value>> standing(Atom atom) {
        return switch (atom) {
            case Atom.Holds(Value value, AnswerAspect aspect) when aspect == AnswerAspect.EMPTINESS ->
                    List.of(Props.same(holds(value), Props.compared(
                            Props.minus(sizeOf(value), Props.constant(1)), Rel.GE)));
            case Atom.Holds _ -> List.of();
            // How many elements meet it is said where the count is taken, beside the count.
            case Atom.Some(Value container, LawProposition<Value> ofTheElement) -> List.of(
                    Props.either(new LawProposition.SomeElement<>(container, ofTheElement, false),
                            holds(container)));
            case Atom.Alike _ -> List.of();
        };
    }

    private static List<LawProposition<Value>> standing(LawNumber<Value> number) {
        return switch (number) {
            case LawNumber.SizeOf<Value> _ ->
                    List.of(Props.compared(LinearForm.atom(number), Rel.GE));
            case LawNumber.HowManyMeet<Value>(Value container, LawProposition<Value> ofTheElement)
                    when container instanceof Value.Listed(List<Value> alone)
                    && alone.size() == 1 -> List.of(Props.either(
                            Props.both(ofTheElement, Props.compared(Props.minus(
                                    LinearForm.atom(number), Props.constant(1)), Rel.EQ)),
                            Props.both(ofTheElement.denied(), Props.compared(
                                    LinearForm.atom(number), Rel.EQ))));
            case LawNumber.HowManyMeet<Value>(Value container, LawProposition<Value> ofTheElement)
                    -> List.of(
                    Props.compared(LinearForm.atom(number), Rel.GE),
                    Props.compared(Props.minus(sizeOf(container), LinearForm.atom(number)),
                            Rel.GE),
                    Props.same(new LawProposition.SomeElement<>(container, ofTheElement, true),
                            Props.compared(Props.minus(LinearForm.atom(number),
                                    Props.constant(1)), Rel.GE)));
            case LawNumber.AnArgument<Value> _ -> List.of();
        };
    }

    private static LawProposition<Value> holds(Value value) {
        return new LawProposition.Observed<>(new LawSubject.Argument<>(value),
                new SideAnswered(AnswerAspect.EMPTINESS, true));
    }

    private static LinearForm<LawNumber<Value>> sizeOf(Value value) {
        return LinearForm.atom(new LawNumber.SizeOf<>(new LawSubject.Argument<>(value)));
    }

    // --- numbers as the numeric domain holds them -----------------------------------------------

    private LinearForm<Integer> numbered(LinearForm<LawNumber<Value>> form) {
        Map<Integer, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((number, coef) -> coefs.put(idOf(number), coef));
        return new LinearForm<>(form.constant(), coefs);
    }

    private Map<Integer, Granularity> spacings(LinearForm<LawNumber<Value>> form) {
        Map<Integer, Granularity> out = new HashMap<>();
        form.coefs().keySet().forEach(number -> out.put(idOf(number), switch (number) {
            case LawNumber.SizeOf<Value> _, LawNumber.HowManyMeet<Value> _ -> Granularity.DISCRETE;
            case LawNumber.AnArgument<Value>(Value value) -> spacing.apply(value);
        }));
        return out;
    }

    private int idOf(LawNumber<Value> number) {
        return numbers.computeIfAbsent(number, _ -> numbers.size());
    }
}
