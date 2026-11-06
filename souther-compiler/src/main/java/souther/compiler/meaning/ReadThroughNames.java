package souther.compiler.meaning;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.HeldIn;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
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
                : innermost(position, names) == null ? had : identityAt(position, names),
                twoAsOne);
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
     */
    public static Proposition toldAgain(Proposition stated, ElementsNamed names) {
        return told(stated, (position, had) -> {
            if (!(had instanceof ValueIdentity.OfAnElement)) {
                return had;
            }
            Set<BindingId> stood = innermost(position, names);
            return stood != null && stood.size() == 1
                    ? new ValueIdentity.OfAnElement(stood.iterator().next()) : had;
        }, () -> stated);
    }

    /**
     * The value at {@code at} that something read through {@code names} is about, as a subject:
     * told the name that stood for its element, as a statement read through the same names is
     * ({@link #readThrough}). Where more than one name stood for it, it is the value at the
     * position, which tells it from no other.
     */
    public static DecisionSubject.AnInput theInputAt(TermPath at, ElementsNamed names) {
        ValueIdentity identity = identityAt(at, names);
        return new DecisionSubject.AnInput(at,
                identity == null ? ValueIdentity.AT_THE_POSITION : identity);
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

    /** {@code relation} said at positions alone ({@link #atThePositions(Proposition)}). */
    public static Relation atThePositions(Relation relation) {
        Relation out = told(relation, (position, had) -> ValueIdentity.AT_THE_POSITION);
        return out == null ? relation : out;
    }

    /**
     * Which value at {@code position} an expression read through {@code names} is about: the one
     * the name of its innermost element stood for, the value at the position where it is in no
     * element a name stood for, and null where more than one name stood for that element.
     */
    public static ValueIdentity identityAt(TermPath position, ElementsNamed names) {
        Set<BindingId> stood = innermost(position, names);
        if (stood == null) {
            return ValueIdentity.AT_THE_POSITION;
        }
        return stood.size() == 1 ? new ValueIdentity.OfAnElement(stood.iterator().next()) : null;
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
                ElementsNamed.Slot slot = innermostSlot(position);
                if (slot != null) {
                    found.add(new ElementsNamed.Named(slot, name));
                }
            }
            return had;
        }, () -> stated);
        return ElementsNamed.of(found);
    }

    /** The innermost element of a container {@code position} is in, or null where it is in
     *  none. */
    private static ElementsNamed.Slot innermostSlot(TermPath position) {
        List<TermPath.Step> steps = position.steps();
        for (int at = steps.size() - 1; at >= 0; at--) {
            HeldIn.Part part = partAt(steps.get(at));
            if (part != null) {
                return new ElementsNamed.Slot(
                        new InputReads.ContainerOf.AtAPosition(position.prefix(at)), part);
            }
        }
        return null;
    }

    private static HeldIn.Part partAt(TermPath.Step step) {
        return switch (step) {
            case TermPath.Step.Element _ -> HeldIn.Part.ELEMENT;
            case TermPath.Step.Key _ -> HeldIn.Part.KEY;
            case TermPath.Step.Field _, TermPath.Step.Refine _ -> null;
        };
    }

    /**
     * The names {@code names} holds for the innermost element of a container {@code position} is
     * in, or null where it holds none for that one or the position is in no element.
     *
     * <p>That element and no outer one: a value inside an element of a container held by another
     * element is a value of the inner element, and the outer element's name says which outer
     * element it is in and not which inner one. Where no name stood for the inner element it is the
     * element of whatever goes over it, and is told nothing.
     */
    private static Set<BindingId> innermost(TermPath position, ElementsNamed names) {
        ElementsNamed.Slot slot = innermostSlot(position);
        return slot == null ? null : names.named().get(slot);
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
            // Shapes over elements of their own: the end a walk keeps, the nodes a search
            // reaches, the ways a statement is written. What they go over is theirs, as a
            // quantifier's element is, and they are left as they stand.
            case Proposition.LastToHold _, Proposition.OfTheWays _, Proposition.Carried _,
                 Proposition.SomeReachable _ -> stated;
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
     * {@code quantity} told which value it is, or null where it is no one: a number of the input,
     * the numbers a remainder is of, the container a count counts the elements of. What a count
     * asks of each element is about its own element, as a quantifier's is; a number of another
     * kind — an end a walk keeps, the values a count takes apart — is over elements of its own.
     */
    private static Quantity told(Quantity quantity, Telling telling) {
        return switch (quantity) {
            case DecisionAtom.OfTheInput(NumericTerm term, ValueIdentity had) -> {
                ValueIdentity told = telling.of(term.subjectPath(), had);
                yield told == null ? null : told.equals(had) ? quantity
                        : new DecisionAtom.OfTheInput(term, told);
            }
            case Quantity.RemainderOfADividend(var operation, LinearForm<Quantity> dividend,
                                               var divisor) -> {
                LinearForm<Quantity> told = told(dividend, telling);
                yield told == null ? null : told == dividend ? quantity
                        : new Quantity.RemainderOfADividend(operation, told, divisor);
            }
            case Quantity.HowManyMeet(DecisionSubject container, Proposition ofTheElement) -> {
                DecisionSubject told = told(container, telling);
                if (told == null) {
                    yield null;
                }
                Proposition element = told(ofTheElement, ownElementLeftAlone(container, telling),
                        () -> null);
                yield element == null ? null
                        : told == container && element == ofTheElement ? quantity
                        : new Quantity.HowManyMeet(told, element);
            }
            default -> quantity;
        };
    }
}
