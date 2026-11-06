package souther.compiler.meaning;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.function.Supplier;

/**
 * A statement with every number and subject at an element's position told which value there it is
 * about: the one the name that stood for the element was given.
 *
 * <p>A position inside a container's elements says an element and not which one, so what a
 * statement read through {@code a} says of {@code xs[*].n} and what one read through {@code b}
 * says of it are about two values at one position. Told apart here, where the part is concluded
 * and the names it was read through are known, they stay two however the statement is put
 * together afterwards; told apart nowhere, a conjunction of the two reads as one value asked two
 * things.
 *
 * <p>A part whose position more than one name stood for is a part nothing read, and nothing else:
 * the rest of the statement stays what it was.
 *
 * <p><b>Who a name is told by.</b> Only by what the statement was read under: a name free in the
 * expression read, a name some construct outside it bound. A name a construct inside the
 * statement binds belongs to that construct — what stands at a quantifier's container's element
 * is the quantifier's element ({@link #ownedBy}), and the positions a count, a walk's kept end or
 * a search holds are the elements that shape goes over — and is left at the position, inside the
 * construct that owns it and nowhere else. Two such positions at one place are therefore about one
 * value only inside one owner; the elements told here never are.
 */
public final class ReadThroughNames {

    private ReadThroughNames() {}

    /** Which value at a position a number or a subject there is, or null where it is no one. */
    private interface Telling {
        ValueIdentity of(TermPath position, ValueIdentity had);
    }

    /**
     * {@code stated} with each number and subject at an element of a container {@code names}
     * holds told the name that stood for it; a part at one more than one name stood for is
     * {@code twoAsOne}.
     */
    static Proposition readThrough(Proposition stated, ElementsNamed names,
                                   Supplier<Proposition> twoAsOne) {
        if (names.isEmpty()) {
            return stated;
        }
        return told(stated, (position, had) -> had instanceof ValueIdentity.OfAnElement ? had
                : identityAt(position, names), twoAsOne);
    }

    /**
     * {@code element}, what a shape over {@code container} — a quantifier, a count — says of the
     * element it goes over, held to that element being the shape's own: at it, a part told a name
     * the shape was {@code given} from outside is {@code twoAsOne}, and one told another name is
     * the shape's element.
     *
     * <p>What the shape's closure binds is read inside the shape's own scope and told no name, or,
     * read through a call inside the shape, the name the closure gave it — a name the shape was
     * not handed. A name it was handed is another element of the container, which a statement of
     * the shape's element has no place for. A shape that does not say what it was handed is
     * handed every name.
     */
    static Proposition ownedBy(DecisionSubject container, Predicate<BindingId> given,
                               Proposition element, Supplier<Proposition> twoAsOne) {
        if (!(container instanceof DecisionSubject.AnInput(TermPath at, var _))) {
            return element;
        }
        TermPath own = at.element();
        TermPath key = at.key();
        return told(element, (position, had) -> {
            if (!(had instanceof ValueIdentity.OfAnElement(BindingId name))
                    || !(position.isAtOrUnder(own) || position.isAtOrUnder(key))) {
                return had;
            }
            return given.test(name) ? null : ValueIdentity.AT_THE_POSITION;
        }, twoAsOne);
    }

    /**
     * {@code stated} said at positions alone, every number and subject told no value there: what
     * a reader holding what a derivation stated, before any name was told, keys the same
     * statement by.
     */
    public static Proposition atThePositions(Proposition stated) {
        return told(stated, (position, had) -> ValueIdentity.AT_THE_POSITION, () -> stated);
    }

    /**
     * {@code stated}, what a site states, told through the names another copy of the site reads:
     * each number and subject told an element is told the name that stands for the element at its
     * position in {@code names} instead.
     *
     * <p>Copies of one site bind names of their own, and what the site states was told the names
     * of the copy it was read off. Within one site each element it was told is the one element
     * the site reads at that position, so the copy's name there is that element's. One the copy
     * reads through no one name keeps the name it was told, which is no name of the copy's: a
     * reader of the copy finds nothing it is about.
     *
     * <p>Where the names told again would tell two values one name — two of the site's met by one
     * of the copy's, or one told the copy's name a name the site keeps already has — the site keeps
     * all its names ({@link #renamedOneToOne}).
     */
    public static Proposition toldAgain(Proposition stated, ElementsNamed names) {
        // Each name the site was told and the copy's name for the element it stood for, where the
        // copy reads that element through one name wherever the site was told it.
        Map<BindingId, Set<BindingId>> copiesOf = new LinkedHashMap<>();
        Set<BindingId> toNone = new HashSet<>();
        told(stated, (position, had) -> {
            if (had instanceof ValueIdentity.OfAnElement(BindingId name)) {
                if (identityAt(position, names) instanceof ValueIdentity.OfAnElement(
                        BindingId copy)) {
                    copiesOf.computeIfAbsent(name, _ -> new HashSet<>()).add(copy);
                } else {
                    toNone.add(name);
                }
            }
            return had;
        }, () -> stated);
        Map<BindingId, BindingId> renaming = new LinkedHashMap<>();
        copiesOf.forEach((name, copies) -> {
            if (!toNone.contains(name) && copies.size() == 1) {
                renaming.put(name, copies.iterator().next());
            }
        });
        Proposition again = renamedOneToOne(stated, renaming);
        return again == null ? stated : again;
    }

    /**
     * {@code stated} with each name {@code renaming} holds told the name it maps to and every other
     * name kept, or null where that tells two of its values one name: where the names it holds come
     * to fewer once renamed, counted over all of them, the ones kept as well as the ones renamed.
     *
     * <p>The one place a statement's names are told others, so that every reader that renames asks
     * the same of the statement it makes and not of a list of names beside it.
     */
    private static Proposition renamedOneToOne(Proposition stated,
                                               Map<BindingId, BindingId> renaming) {
        if (renaming.isEmpty()) {
            return stated;
        }
        Set<BindingId> before = new HashSet<>();
        told(stated, (position, had) -> {
            if (had instanceof ValueIdentity.OfAnElement(BindingId name)) {
                before.add(name);
            }
            return had;
        }, () -> stated);
        Set<BindingId> after = new HashSet<>();
        for (BindingId each : before) {
            after.add(renaming.getOrDefault(each, each));
        }
        if (after.size() != before.size()) {
            return null;
        }
        return told(stated, (position, had) ->
                had instanceof ValueIdentity.OfAnElement(BindingId name)
                        && renaming.get(name) instanceof BindingId to
                        ? new ValueIdentity.OfAnElement(to) : had, () -> stated);
    }

    /**
     * {@code stated} holding one value at each element's position: the first value met at it is
     * kept, and a part that reads another value there is {@code twoAsOne} — that part, and the
     * rest as it stood. What a quantifier or a count says of its own element is its own and is
     * left out.
     *
     * <p>What a statement is handed on to is read at positions — a row a reading writes holds one
     * value at each, a region is of the values at positions, a form is over the numbers at them —
     * so a statement holding two values at one position is said there as one value asked two
     * things, which is a run that takes both read as none. Held to one value at each before it is
     * handed on, no reader of positions can meet two, whatever it keys by; the values it holds are
     * still told apart, so what two statements hold of two elements stays two.
     */
    public static Proposition oneValueAtEachElement(Proposition stated,
                                                    Supplier<Proposition> twoAsOne) {
        Map<ElementsNamed.Slot, ValueIdentity> first = new HashMap<>();
        return told(stated, (position, had) -> {
            ElementsNamed.Slot slot = ElementsNamed.Slot.innermostOf(position);
            if (slot == null) {
                return had;
            }
            ValueIdentity was = first.putIfAbsent(slot, had);
            return was == null || was.equals(had) ? had : null;
        }, twoAsOne);
    }

    /** Whether {@code stated} holds one value at each element's position
     *  ({@link #oneValueAtEachElement}): what a reader of positions can be handed. */
    public static boolean holdsOneValueAtEachElement(Proposition stated) {
        boolean[] two = {false};
        oneValueAtEachElement(stated, () -> {
            two[0] = true;
            return stated;
        });
        return !two[0];
    }

    /**
     * Whether {@code one} and {@code other} state the same thing of the same values, whatever the
     * names each was told: the same at positions, and the values each was told met in the same
     * places one to one — the same value wherever one has the same value, and another wherever it
     * has another. A value at the position stands only for itself.
     *
     * <p>Shown by telling {@code one} the names of {@code other} one to one and finding the very
     * statement {@code other} is, each part told the name the same part of {@code other} is. The
     * names are paired in the order they stand, and that order is only where the pairing comes
     * from: a statement orders its parts by what they spell, names and all, so the same place can
     * come at another turn. A pairing that does not make {@code other} shows nothing.
     *
     * <p>Where that cannot be shown they are said to differ, which is never the wrong way round:
     * two statements of different values taken for one would be one value's two names.
     */
    public static boolean sameUpToTheNames(Proposition one, Proposition other) {
        if (one.equals(other)) {
            return true;
        }
        if (!atThePositions(one).equals(atThePositions(other))) {
            return false;
        }
        List<ValueIdentity> ofOne = identitiesIn(one);
        List<ValueIdentity> ofOther = identitiesIn(other);
        if (ofOne.size() != ofOther.size()) {
            return false;
        }
        Map<BindingId, BindingId> renaming = new LinkedHashMap<>();
        for (int at = 0; at < ofOne.size(); at++) {
            if (ofOne.get(at) instanceof ValueIdentity.OfAnElement(BindingId mine)
                    && ofOther.get(at) instanceof ValueIdentity.OfAnElement(BindingId theirs)) {
                BindingId was = renaming.putIfAbsent(mine, theirs);
                if (was != null && !was.equals(theirs)) {
                    return false;
                }
            }
        }
        Proposition told = renamedOneToOne(one, renaming);
        return told != null && told.equals(other);
    }

    /** The value each number and subject of {@code stated} was told, in the order they stand. */
    private static List<ValueIdentity> identitiesIn(Proposition stated) {
        List<ValueIdentity> out = new ArrayList<>();
        told(stated, (position, had) -> {
            out.add(had);
            return had;
        }, () -> stated);
        return out;
    }

    /**
     * The value at {@code at} that something read through {@code names} is about, as a subject:
     * told the name that stood for its element, as a statement read through the same names is
     * ({@link #readThrough}). Asked only where every element was read as one value
     * ({@link ElementsNamed#readsNoOneValue}).
     */
    public static DecisionSubject.AnInput theInputAt(TermPath at, ElementsNamed names) {
        ValueIdentity identity = identityAt(at, names);
        if (identity == null) {
            throw new IllegalArgumentException("what was read is of no one value at " + at
                    + ": " + names);
        }
        return new DecisionSubject.AnInput(at, identity);
    }

    /** The number at {@code term} that something read through {@code names} is about
     *  ({@link #theInputAt}). */
    public static DecisionAtom.OfTheInput theNumberAt(NumericTerm term, ElementsNamed names) {
        return new DecisionAtom.OfTheInput(term,
                theInputAt(term.subjectPath(), names).identity());
    }

    /** {@code form}, over the numbers that something read through {@code names} is about
     *  ({@link #theNumberAt}). */
    public static LinearForm<DecisionAtom> theNumbersOf(LinearForm<NumericTerm> form,
                                                       ElementsNamed names) {
        Map<DecisionAtom, ExactRatio> coefs = new LinkedHashMap<>();
        // Each atom holds its term, so two terms are never one atom.
        form.coefs().forEach((term, coefficient) ->
                coefs.put(theNumberAt(term, names), coefficient));
        return new LinearForm<>(form.constant(), coefs);
    }

    /**
     * {@code quantity} said at positions alone ({@link #atThePositions(Proposition)}): for a reader
     * asking where a number stands, and not which value there it is. A number made of two values
     * at one position is no number at positions, and is as it was.
     */
    public static Quantity atThePositions(Quantity quantity) {
        Quantity out = told(quantity, (position, had) -> ValueIdentity.AT_THE_POSITION);
        return out == null ? quantity : out;
    }

    /** {@code form} said at positions alone ({@link #atThePositions(Quantity)}). */
    public static LinearForm<Quantity> atThePositions(LinearForm<Quantity> form) {
        LinearForm<Quantity> out = told(form, (position, had) -> ValueIdentity.AT_THE_POSITION);
        return out == null ? form : out;
    }

    /** {@code subject} said at its position alone ({@link #atThePositions(Quantity)}). */
    public static DecisionSubject atThePositions(DecisionSubject subject) {
        return told(subject, (position, had) -> ValueIdentity.AT_THE_POSITION);
    }

    /** {@code relation} said at positions alone ({@link #atThePositions(Proposition)}). */
    public static Relation atThePositions(Relation relation) {
        Relation out = told(relation, (position, had) -> ValueIdentity.AT_THE_POSITION);
        return out == null ? relation : out;
    }

    /**
     * Which value at {@code position} an expression read through {@code names} is about: the one
     * the name of its innermost element stood for, the value at the position where it is in no
     * element a name stood for, and null where that element is of no one value — more than one
     * name stood for it, or a name whose element is not known ({@link ElementsNamed#noOneValueAt}).
     *
     * <p>That element and no outer one: a value inside an element of a container held by another
     * element is a value of the inner element, and the outer element's name says which outer
     * element it is in and not which inner one. Where no name stood for the inner element it is the
     * element of whatever goes over it, and is told nothing.
     */
    public static ValueIdentity identityAt(TermPath position, ElementsNamed names) {
        ElementsNamed.Slot slot = ElementsNamed.Slot.innermostOf(position);
        if (slot == null) {
            return ValueIdentity.AT_THE_POSITION;
        }
        if (names.noOneValueAt(slot)) {
            return null;
        }
        Set<BindingId> stood = names.named().get(slot);
        return stood == null ? ValueIdentity.AT_THE_POSITION
                : new ValueIdentity.OfAnElement(stood.iterator().next());
    }

    /**
     * Which elements the numbers and subjects of {@code stated} were told they are about, each by
     * the container its position is the element of: what a reader that says {@code stated} at
     * positions keeps beside it, to tell two statements at one position apart.
     */
    public static ElementsNamed namedIn(Proposition stated) {
        List<ElementsNamed.Named> found = new ArrayList<>();
        told(stated, (position, had) -> {
            if (had instanceof ValueIdentity.OfAnElement(BindingId name)) {
                ElementsNamed.Slot slot = ElementsNamed.Slot.innermostOf(position);
                if (slot != null) {
                    found.add(new ElementsNamed.Named(slot, name));
                }
            }
            return had;
        }, () -> stated);
        return ElementsNamed.of(found);
    }

    private static Proposition told(Proposition stated, Telling telling,
                                    Supplier<Proposition> twoAsOne) {
        return switch (stated) {
            case Proposition.Always _, Proposition.Unread _ -> stated;
            case Proposition.Compared compared -> {
                Relation relation = told(compared.relation(), telling);
                yield relation == null ? twoAsOne.get()
                        : relation == compared.relation() ? stated
                        : new Proposition.Compared(relation, compared.holds());
            }
            case Proposition.Truth truth -> {
                DecisionSubject of = told(truth.of(), telling);
                yield of == null ? twoAsOne.get() : of == truth.of() ? stated
                        : new Proposition.Truth(of, truth.holds());
            }
            case Proposition.InCases cases -> {
                DecisionSubject of = told(cases.of(), telling);
                yield of == null ? twoAsOne.get() : of == cases.of() ? stated
                        : new Proposition.InCases(of, cases.cases(), cases.holds());
            }
            case Proposition.Present present -> {
                DecisionSubject of = told(present.of(), telling);
                yield of == null ? twoAsOne.get() : of == present.of() ? stated
                        : new Proposition.Present(of, present.holds());
            }
            case Proposition.SameValue same -> {
                DecisionSubject one = told(same.one(), telling);
                DecisionSubject other = told(same.other(), telling);
                yield one == null || other == null ? twoAsOne.get()
                        : one == same.one() && other == same.other() ? stated
                        : new Proposition.SameValue(one, other, same.holds());
            }
            // A statement none of whose parts was told anything is the statement it was, and is
            // not put together again: joining parts orders them, which is no small thing to do
            // for each statement a reader tells.
            case Proposition.All all -> {
                List<Proposition> parts = eachTold(all.parts(), telling, twoAsOne);
                yield parts == null ? stated : Proposition.all(parts);
            }
            case Proposition.Any any -> {
                List<Proposition> parts = eachTold(any.parts(), telling, twoAsOne);
                yield parts == null ? stated : Proposition.any(parts);
            }
            case Proposition.WhereItAnswers where -> {
                Proposition answers = told(where.answers(), telling, twoAsOne);
                Proposition states = told(where.states(), telling, twoAsOne);
                yield answers == where.answers() && states == where.states() ? stated
                        : Proposition.whereItAnswers(answers, states);
            }
            case Proposition.OnAnApplication applied -> {
                List<Proposition> each = eachTold(applied.each(), telling, twoAsOne);
                yield each == null ? stated : Proposition.onAnApplication(each);
            }
            // Inside a quantifier its container's element is its own, and stays as it stands: a
            // name read there for another element of the container was refused where it was
            // read. The container itself is told as any subject is.
            case Proposition.Some some -> {
                DecisionSubject container = told(some.container(), telling);
                if (container == null) {
                    yield twoAsOne.get();
                }
                Proposition element = told(some.ofTheElement(), ownElementLeftAlone(
                        some.container(), telling), twoAsOne);
                yield container == some.container() && element == some.ofTheElement() ? stated
                        : new Proposition.Some(container, element, some.holds());
            }
            // A string at a position is a subject as any other is.
            case Proposition.InTheStrings strings -> {
                if (!(strings.of() instanceof Proposition.InTheStrings.Strings.AtAPosition(
                        TermPath at, ValueIdentity had))) {
                    yield stated;
                }
                ValueIdentity identity = telling.of(at, had);
                yield identity == null ? twoAsOne.get() : identity.equals(had) ? stated
                        : new Proposition.InTheStrings(
                                new Proposition.InTheStrings.Strings.AtAPosition(at, identity),
                                strings.accepts(), strings.holds());
            }
            // A string inside another is a relation of the two strings' values.
            case Proposition.StringInside inside -> {
                Quantity inner = told(inside.inner(), telling);
                Quantity outer = told(inside.outer(), telling);
                yield inner == null || outer == null ? twoAsOne.get()
                        : inner == inside.inner() && outer == inside.outer() ? stated
                        : new Proposition.StringInside(inner, outer, inside.where(),
                                inside.holds());
            }
            // How many of some statements hold is of whatever those statements are of.
            case Proposition.SoManyHold many -> {
                List<Proposition> statements = eachTold(many.statements(), telling, twoAsOne);
                yield statements == null ? stated : Proposition.SoManyHold.counting(statements,
                        many.weights(), many.admitted());
            }
            // The end a walk keeps is of the walk's own elements; the container it walks is a
            // subject as any other.
            case Proposition.LastToHold last -> {
                DecisionSubject container = told(last.container(), telling);
                yield container == null ? twoAsOne.get() : container == last.container() ? stated
                        : new Proposition.LastToHold(container, last.position(), last.holds());
            }
            // Statements that hold their places with no word of which value at them they are
            // about — the nodes a search reaches, the ways a statement is written: as they stand
            // where none of their places is one a name was told, and a part nothing read where
            // one is, rather than said of the value at the place.
            case Proposition.OfTheWays _, Proposition.SomeReachable _ -> {
                List<TermPath> places = PositionsAStatementReads.everyPlaceOf(stated)
                        .orElse(List.of());
                for (TermPath at : places) {
                    if (!ValueIdentity.AT_THE_POSITION.equals(
                            telling.of(at, ValueIdentity.AT_THE_POSITION))) {
                        yield twoAsOne.get();
                    }
                }
                yield stated;
            }
            case Proposition.Carried _ -> stated;
        };
    }

    /** Each of {@code parts} told, or null where none of them was told anything. */
    private static List<Proposition> eachTold(List<Proposition> parts, Telling telling,
                                              Supplier<Proposition> twoAsOne) {
        List<Proposition> out = new ArrayList<>(parts.size());
        boolean changed = false;
        for (Proposition each : parts) {
            Proposition told = told(each, telling, twoAsOne);
            changed |= told != each;
            out.add(told);
        }
        return changed ? out : null;
    }

    /** {@code telling}, with what stands at {@code container}'s element left as it is. */
    private static Telling ownElementLeftAlone(DecisionSubject container, Telling telling) {
        if (!(container instanceof DecisionSubject.AnInput(TermPath at, var _))) {
            return telling;
        }
        TermPath own = at.element();
        TermPath key = at.key();
        return (position, had) -> position.isAtOrUnder(own) || position.isAtOrUnder(key) ? had
                : telling.of(position, had);
    }

    /** {@code subject} told which value it is, or null where it is no one. */
    private static DecisionSubject told(DecisionSubject subject, Telling telling) {
        if (!(subject instanceof DecisionSubject.AnInput(TermPath at, ValueIdentity had))) {
            return subject;
        }
        ValueIdentity told = telling.of(at, had);
        return told == null ? null : told.equals(had) ? subject
                : new DecisionSubject.AnInput(at, told);
    }

    /** {@code relation} with each number of the input told which value it is, or null where one
     *  is no one, or where a number of another kind reads a position told. */
    private static Relation told(Relation relation, Telling telling) {
        return switch (relation) {
            case Relation.Affine(LinearForm<Quantity> form, Rel rel) -> {
                LinearForm<Quantity> told = told(form, telling);
                yield told == null ? null : told == form ? relation
                        : new Relation.Affine(told, rel);
            }
            case Relation.Ordered(DecisionAtom term, var at, Rel rel) -> {
                Quantity told = told(term, telling);
                yield told == null ? null : told == term ? relation
                        : new Relation.Ordered((DecisionAtom) told, at, rel);
            }
        };
    }

    /** {@code form} with each of its numbers told which value it is, itself where none is told
     *  anything, or null where one is no one or two are told to be one number. */
    private static LinearForm<Quantity> told(LinearForm<Quantity> form, Telling telling) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        boolean changed = false;
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            Quantity term = told(each.getKey(), telling);
            // Two numbers told to be one are no form this says.
            if (term == null || coefs.containsKey(term)) {
                return null;
            }
            changed |= term != each.getKey();
            coefs.put(term, each.getValue());
        }
        return changed ? new LinearForm<>(form.constant(), coefs) : form;
    }

    /**
     * {@code quantity} told which value it is, or null where it is no one.
     *
     * <p>Every kind of number, named one by one: a number of the input, and every number made of
     * one — what an operation answers of one, a piece of a string, a remainder, a count of the
     * elements of a container, a sum over them. What a count or a sum asks of each element is about
     * its own element, as a quantifier's is, and is left as it is there. A kind that holds a
     * position and has no place to say which value there it is about is no one number where the
     * position is one a name was told: it is read as nothing rather than as the value at the
     * position, which another element's number would be too.
     */
    private static Quantity told(Quantity quantity, Telling telling) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(NumericTerm term, ValueIdentity had) -> {
                ValueIdentity told = telling.of(term.subjectPath(), had);
                yield told == null ? null : told.equals(had) ? quantity
                        : new DecisionAtom.OfTheInput(term, told);
            }
            // Of what a dependency answered, or of nothing a row writes.
            case DecisionAtom.TakenOfAnAnswer _, DecisionAtom.ComputedOverAnAnswer _,
                 DecisionAtom.OfAnAnswer _, Quantity.HowManyCarried _, Quantity.TheKeptTotal _,
                 Quantity.CodePointsOfAPiece _ -> quantity;
            case Quantity.WhatAnOperationAnswers(var operation, List<Quantity> of) -> {
                List<Quantity> told = told(of, telling);
                yield told == null ? null : told == of ? quantity
                        : new Quantity.WhatAnOperationAnswers(operation, told);
            }
            case Quantity.APieceOf(var operation, var separator, Quantity string, var within,
                                   int from, int among) -> {
                Quantity told = told(string, telling);
                yield told == null ? null : told == string ? quantity
                        : new Quantity.APieceOf(operation, separator, told, within, from, among);
            }
            case Quantity.ThePieceAt(var operation, int separator, Quantity string, int index) -> {
                Quantity told = told(string, telling);
                yield told == null ? null : told == string ? quantity
                        : new Quantity.ThePieceAt(operation, separator, told, index);
            }
            case Quantity.IsAmongThePieces(Quantity value, var operation, var separator,
                                           Quantity string, int from, int among) -> {
                Quantity toldValue = told(value, telling);
                Quantity toldString = told(string, telling);
                yield toldValue == null || toldString == null ? null
                        : toldValue == value && toldString == string ? quantity
                        : new Quantity.IsAmongThePieces(toldValue, operation, separator,
                                toldString, from, among);
            }
            case Quantity.RemainderOfADividend(var operation, LinearForm<Quantity> dividend,
                                               var divisor) -> {
                LinearForm<Quantity> told = told(dividend, telling);
                yield told == null ? null : told == dividend ? quantity
                        : new Quantity.RemainderOfADividend(operation, told, divisor);
            }
            case Quantity.HowManyMeet(DecisionSubject container, Proposition ofTheElement) -> {
                DecisionSubject told = told(container, telling);
                Proposition element = toldWhole(ofTheElement,
                        ownElementLeftAlone(container, telling));
                yield told == null || element == null ? null
                        : told == container && element == ofTheElement ? quantity
                        : new Quantity.HowManyMeet(told, element);
            }
            case Quantity.HowManyHold(List<Proposition> each) -> {
                List<Proposition> told = new ArrayList<>(each.size());
                boolean changed = false;
                for (Proposition one : each) {
                    Proposition toldOne = toldWhole(one, telling);
                    if (toldOne == null) {
                        yield null;
                    }
                    changed |= toldOne != one;
                    told.add(toldOne);
                }
                yield changed ? new Quantity.HowManyHold(told) : quantity;
            }
            case Quantity.SumOver(DecisionSubject container, Quantity ofTheElement) -> {
                DecisionSubject told = told(container, telling);
                Quantity element = told(ofTheElement, ownElementLeftAlone(container, telling));
                yield told == null || element == null ? null
                        : told == container && element == ofTheElement ? quantity
                        : new Quantity.SumOver(told, element);
            }
            // The values counted are of the count's own elements, and left as they are.
            case Quantity.HowManyDifferent(DecisionSubject container, var ofTheElement) -> {
                DecisionSubject told = told(container, telling);
                yield told == null ? null : told == container ? quantity
                        : new Quantity.HowManyDifferent(told, ofTheElement);
            }
            case Quantity.HowManyDifferentAcross(DecisionSubject container, var occurrence) -> {
                DecisionSubject told = told(container, telling);
                yield told == null ? null : told == container ? quantity
                        : new Quantity.HowManyDifferentAcross(told, occurrence);
            }
            case Quantity.HowManyDifferentMeet(DecisionSubject container, var ofTheElement,
                                               Quantity.HowManyDifferentMeet.Selection meeting) -> {
                DecisionSubject told = told(container, telling);
                Proposition statement = toldWhole(meeting.statement(),
                        ownElementLeftAlone(container, telling));
                if (told == null || statement == null) {
                    yield null;
                }
                yield told == container && statement == meeting.statement() ? quantity
                        : Quantity.HowManyDifferentMeet.of(told, ofTheElement,
                                meeting instanceof Quantity.HowManyDifferentMeet.Selection
                                        .OfEachValue
                                        ? new Quantity.HowManyDifferentMeet.Selection.OfEachValue(
                                                statement)
                                        : new Quantity.HowManyDifferentMeet.Selection
                                                .OfEachElement(statement));
            }
            case Quantity.RemainderByAnInput(var operation, var dividend, ValueIdentity dividendIs,
                                             var divisor, ValueIdentity divisorIs) -> {
                ValueIdentity one = telling.of(dividend.subjectPath(), dividendIs);
                ValueIdentity other = telling.of(divisor.subjectPath(), divisorIs);
                yield one == null || other == null ? null
                        : one.equals(dividendIs) && other.equals(divisorIs) ? quantity
                        : new Quantity.RemainderByAnInput(operation, dividend, one, divisor,
                                other);
            }
            case Quantity.ProductOfTwo(var one, ValueIdentity oneIs, var other,
                                       ValueIdentity otherIs) -> {
                ValueIdentity first = telling.of(one.subjectPath(), oneIs);
                ValueIdentity second = telling.of(other.subjectPath(), otherIs);
                yield first == null || second == null ? null
                        : first.equals(oneIs) && second.equals(otherIs) ? quantity
                        : new Quantity.ProductOfTwo(one, first, other, second);
            }
            // Kinds that hold positions with no place for which value: the nodes below a node,
            // what a recursion carries.
            case Quantity.HowManyDifferentBelow below ->
                    untold(quantity, List.of(below.root(), below.map()), telling);
            case Quantity.OfABinding binding -> untold(quantity,
                    binding.handed().map(ReadThroughNames::positionsHandedFrom).orElse(List.of()),
                    telling);
        };
    }

    /**
     * {@code stated}, a statement a number is made of, told — or null where some part of it is no
     * one value, which makes the number no one number rather than one holding a part nothing read.
     */
    private static Proposition toldWhole(Proposition stated, Telling telling) {
        boolean[] noOne = {false};
        Proposition out = told(stated, telling, () -> {
            noOne[0] = true;
            return stated;
        });
        return noOne[0] ? null : out;
    }

    /** {@code each} told, itself where none of them is told anything, or null where one is no
     *  one number. */
    private static List<Quantity> told(List<Quantity> each, Telling telling) {
        List<Quantity> out = new ArrayList<>(each.size());
        boolean changed = false;
        for (Quantity one : each) {
            Quantity told = told(one, telling);
            if (told == null) {
                return null;
            }
            changed |= told != one;
            out.add(told);
        }
        return changed ? out : each;
    }

    /**
     * {@code quantity}, which holds {@code positions} and no word of which value at them it is
     * about: itself where none of them is one a name was told, and null — no one number — where
     * one is.
     */
    private static Quantity untold(Quantity quantity, List<TermPath> positions, Telling telling) {
        for (TermPath at : positions) {
            if (at != null && !ValueIdentity.AT_THE_POSITION.equals(
                    telling.of(at, ValueIdentity.AT_THE_POSITION))) {
                return null;
            }
        }
        return quantity;
    }

    /** The positions a value read off a binding was handed from outside the walk that binds it:
     *  the container it walks, and the numbers it starts and ends at. */
    private static List<TermPath> positionsHandedFrom(Quantity.ReadOffABinding handed) {
        List<TermPath> out = new ArrayList<>();
        switch (handed) {
            case Quantity.PickedAtAnIndex picked -> out.add(picked.container());
            case Quantity.PositionInTheWalk walk -> out.add(walk.container());
            case Quantity.KeptSoFar kept -> out.add(kept.container());
            case Quantity.AWholeNumberInTurn turn -> {
                turn.from().coefs().keySet().forEach(term -> out.add(term.subjectPath()));
                turn.to().coefs().keySet().forEach(term -> out.add(term.subjectPath()));
            }
        }
        return out;
    }
}
