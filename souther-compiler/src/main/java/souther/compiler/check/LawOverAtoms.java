package souther.compiler.check;

import souther.compiler.check.Derivation.HoldsSomethingWhere.Holding;
import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;
import java.util.function.Function;

/**
 * What a law of the library says at a call, as the discharge of a rule names it: a statement over
 * the counts and numbers of the arguments ({@link Holding}), and a number as a form over them.
 *
 * <p>The law is taken apart by {@link LawAtACall}, as the reading of an input takes it apart; this
 * answers only the parts that reading leaves to a reader, in the names this side has. A part those
 * names do not reach is held as one ({@link Holding.Unnamed}) and not left out: a law says when
 * something holds and, by the same statement, when it does not, so a part left out would answer the
 * second wrong, and a part held as unnamed settles neither side of itself.
 *
 * <p>Some element meeting a statement is how many meet it being above nought, and how many fail it
 * is how many there are less how many meet it; so every quantifier is a count, and a count is named
 * by what it counts ({@link Terms#howManyMeetFor}) wherever a law or a condition asks it. A
 * string inside another is no number. Which strings a string may be where it holds one is what the
 * reading of a call as a set of strings answers ({@link StringPredicates}); here it is a part
 * unnamed, together with what it makes certain of the numbers: the one inside is no longer than the
 * one around it.
 */
final class LawOverAtoms implements LawAtACall.Reading<Denotations, Holding, LinearForm<FactSubject>> {

    private final AnOperationApplied applied;
    private final Denotations at;
    private final Terms terms;
    private final ElementsWrittenOut.Reading<Denotations> elements;

    private LawOverAtoms(AnOperationApplied applied, Denotations at, Terms terms) {
        this.applied = applied;
        this.at = at;
        this.terms = terms;
        this.elements = terms.elementsReading();
    }

    /**
     * What {@code applied}'s answer coming out on {@code aspect}'s holding side is the same as, read
     * in {@code at} — or null where no law settles that side, or every part of it is one this
     * cannot name.
     */
    static Holding whereItHolds(AnOperationApplied applied, AnswerAspect aspect, Denotations at,
                                Terms terms) {
        if (applied == null) {
            return null;
        }
        Holding read = DefaultBoundOperationFacts.get().settled(applied.operation(),
                OperationLaw.Observed.of(aspect)) instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Observation<DeclaredArgument>(
                                AnswerAspect stated, LawProposition<DeclaredArgument> law),
                        var _) && stated == aspect
                ? LawAtACall.of(law, new LawOverAtoms(applied, at, terms)) : null;
        return read == null || namesNothing(read) ? null : read;
    }

    /** Whether every part of {@code holding} is one this names by nothing, so that it settles
     *  nothing on any path. */
    private static boolean namesNothing(Holding holding) {
        return switch (holding) {
            case Holding.Unnamed _ -> true;
            case Holding.Not(Holding denied) -> namesNothing(denied);
            case Holding.AllOf(var ways) -> !ways.isEmpty()
                    && ways.stream().allMatch(LawOverAtoms::namesNothing);
            case Holding.AnyOf(var ways) -> !ways.isEmpty()
                    && ways.stream().allMatch(LawOverAtoms::namesNothing);
            case Holding.Something _, Holding.Stands _ -> false;
        };
    }

    /**
     * How many {@code applied}'s answer holds, read in {@code at}, where its law says it in one
     * case met whatever the arguments are, or in two told apart by whether a container holding
     * each value once holds one ({@link #byAValueHeldOnce}) — or null where no law says, it says
     * it in other cases ({@link #sizeInCases}), or names a number this cannot.
     */
    static Sized sizeOf(AnOperationApplied applied, Denotations at, Terms terms) {
        OperationLaw.Size<DeclaredArgument> law = sizeLawOf(applied);
        if (law == null) {
            return null;
        }
        LawOverAtoms reading = new LawOverAtoms(applied, at, terms);
        LinearForm<LawNumber<DeclaredArgument>> unconditional = law.unconditional();
        if (unconditional == null) {
            return reading.byAValueHeldOnce(law.cases());
        }
        LinearForm<FactSubject> form = reading.form(unconditional);
        return form == null ? null : new Sized(form, null);
    }

    /**
     * How many an answer holds: the law's one form, or its two cases of a value held once
     * ({@code byTheValue}) — one of the two, and the other null.
     */
    record Sized(LinearForm<FactSubject> form, ByAValueHeldOnce byTheValue) {

        Sized {
            if ((form == null) == (byTheValue == null)) {
                throw new IllegalArgumentException("a size is said by one form or by two cases");
            }
        }

        /**
         * What {@code answer}, the atom of how many the answer holds, is held to whatever the
         * path: the form, or where the law was in cases, the answer between what the two cases
         * come to.
         *
         * <p>The span and not one form of the count. The span relates two atoms each way, which
         * is what a reading closes over, and says what the cases say read forward; which case it
         * is, is what the count settles where a reading settles it ({@link #guaranteedOf}).
         */
        List<NumericConstraint> carriedBy(FactSubject answer) {
            List<NumericConstraint> out = new ArrayList<>();
            if (byTheValue == null) {
                stating(LinearForm.atom(answer).minus(form).orNull(), Rel.EQ, out);
            } else {
                boolean fewerWhereHeld = byTheValue.fewerWhereHeld();
                stating(LinearForm.atom(answer).minus(fewerWhereHeld ? byTheValue.held()
                        : byTheValue.notHeld()).orNull(), Rel.GE, out);
                stating(LinearForm.atom(answer).minus(fewerWhereHeld ? byTheValue.notHeld()
                        : byTheValue.held()).orNull(), Rel.LE, out);
            }
            return out;
        }

        /**
         * What {@code answer} comes to where a reading settles the count: the one case's answer
         * where the value is held, and the other's where it is not. Asked of the reading's bounds
         * on the count and opening no case, so a chain of such operations is read once.
         */
        List<ConditionalConstraint> guaranteedOf(FactSubject answer) {
            if (byTheValue == null) {
                return List.of();
            }
            LinearForm<FactSubject> atLeastOne = byTheValue.count()
                    .minus(LinearForm.constant(ExactRatio.ONE)).orNull();
            LinearForm<FactSubject> asHeld = LinearForm.atom(answer).minus(byTheValue.held())
                    .orNull();
            LinearForm<FactSubject> asNotHeld = LinearForm.atom(answer)
                    .minus(byTheValue.notHeld()).orNull();
            if (atLeastOne == null || asHeld == null || asNotHeld == null) {
                return List.of();
            }
            return List.of(
                    new ConditionalConstraint(new NumericConstraint(atLeastOne, Rel.GE),
                            new NumericConstraint(asHeld, Rel.EQ)),
                    new ConditionalConstraint(new NumericConstraint(byTheValue.count(), Rel.LE),
                            new NumericConstraint(asNotHeld, Rel.EQ)));
        }

        private static void stating(LinearForm<FactSubject> form, Rel rel,
                                    List<NumericConstraint> out) {
            if (form != null) {
                out.add(new NumericConstraint(form, rel));
            }
        }
    }

    /**
     * Two cases of how many an answer holds, told apart by how many of a container that holds
     * each value once are one value: {@code held} where it is one, {@code notHeld} where none is.
     */
    record ByAValueHeldOnce(LinearForm<FactSubject> count, LinearForm<FactSubject> held,
                            LinearForm<FactSubject> notHeld) {

        /** Whether the answer is the smaller where the value is held, as an insert's is. */
        boolean fewerWhereHeld() {
            LinearForm<FactSubject> step = held.minus(notHeld).orNull();
            return step != null && step.constant().signum() < 0;
        }
    }

    /**
     * Two cases that are a container holding one value, or not, where the container holds each
     * value once — a set its elements, a map its keys — and the two answers differ by a number.
     *
     * <p>Not cases to open. The answer lies between the two whichever holds, and is the one the
     * count picks where a reading settles the count; read as cases, every value built by a chain
     * of such operations is a split in each reading that bounds it, for a count no reading may
     * say anything of.
     */
    private Sized byAValueHeldOnce(List<OperationLaw.Size.Case<DeclaredArgument>> cases) {
        if (cases.size() != 2) {
            return null;
        }
        LinearForm<FactSubject> count = null;
        LinearForm<FactSubject> held = null;
        LinearForm<FactSubject> notHeld = null;
        for (OperationLaw.Size.Case<DeclaredArgument> each : cases) {
            if (!(each.where() instanceof LawProposition.SomeElement<DeclaredArgument> some)
                    || !heldOnce(some)) {
                return null;
            }
            LinearForm<FactSubject> answer = form(each.equalTo());
            LinearForm<FactSubject> counted = switch (LawAtACall.of(each.where(), this)) {
                case Holding.Something(LinearForm<FactSubject> c) -> c;
                case Holding.Not(Holding.Something(LinearForm<FactSubject> c)) -> c;
                case null, default -> null;
            };
            if (answer == null || counted == null || (count != null && !count.equals(counted))) {
                return null;
            }
            count = counted;
            if (some.holds()) {
                held = answer;
            } else {
                notHeld = answer;
            }
        }
        LinearForm<FactSubject> step = held == null || notHeld == null ? null
                : held.minus(notHeld).orNull();
        return step == null || !step.coefs().isEmpty() ? null
                : new Sized(null, new ByAValueHeldOnce(count, held, notHeld));
    }

    /** Whether {@code some} asks of a container that holds each value once: some element of a
     *  set being a value, or some key of a map. */
    private boolean heldOnce(LawProposition.SomeElement<DeclaredArgument> some) {
        Core container = applied.argument(some.container());
        if (container == null || !(some.ofTheElement() instanceof LawProposition.Same<
                DeclaredArgument>(var one, var other, boolean same)) || !same) {
            return false;
        }
        AddsWhatItDoesNotHold.Of once = AddsWhatItDoesNotHold.Of.heldOnceIn(
                TypeOps.base(Core.withoutStanding(container).type(), terms.newtypeInners()));
        LawSubject<DeclaredArgument> asked = once == null ? null : heldAs(some.container(), once);
        return asked != null && (asked.equals(one) || asked.equals(other));
    }

    /**
     * How many {@code applied}'s answer holds, read in {@code at}, where its law says it case by
     * case: one arm for each case, answering what the case comes to and settled by what its
     * condition makes certain — or null where no law says it so, or a case comes to a number this
     * cannot name.
     *
     * <p>Which case it is, is the domain's to say and not this: {@code List.take(2, [1, 2, 3])}
     * holds two because a list of three is no shorter than two, which is what the size of
     * {@code [1, 2, 3]} is known to be, and {@code List.take(c, [1, 2, 3])} holds {@code c} or
     * three by where {@code c} stands. A case whose condition cannot hold is no arm; one whose
     * condition this cannot name is an arm settled by nothing, which can only widen where the value
     * may lie.
     */
    static Derivation.Chosen sizeInCases(AnOperationApplied applied, Denotations at,
                                         Terms terms) {
        OperationLaw.Size<DeclaredArgument> law = sizeLawOf(applied);
        if (law == null || law.unconditional() != null) {
            return null;
        }
        LawOverAtoms reading = new LawOverAtoms(applied, at, terms);
        if (reading.byAValueHeldOnce(law.cases()) != null) {
            return null;
        }
        List<Derivation.Chosen.Arm> arms = new ArrayList<>();
        for (OperationLaw.Size.Case<DeclaredArgument> each : law.cases()) {
            LinearForm<FactSubject> answer = reading.form(each.equalTo());
            if (answer == null) {
                return null;
            }
            Holding where = LawAtACall.of(each.where(), reading);
            List<NumericConstraint> settles = where == null ? List.of() : certain(where, true);
            if (settles != null) {
                arms.add(new Derivation.Chosen.Arm(answer, settles));
            }
        }
        return arms.isEmpty() ? null : new Derivation.Chosen(arms);
    }

    /** The law {@code applied}'s operation is settled how many it holds by, or null where none. */
    private static OperationLaw.Size<DeclaredArgument> sizeLawOf(AnOperationApplied applied) {
        return applied != null && DefaultBoundOperationFacts.get().settled(applied.operation(),
                OperationLaw.Observed.SIZE) instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Size<DeclaredArgument> law, var _) ? law : null;
    }

    /** Whether {@code holding} comes out the same whatever the counts and numbers are, and which
     *  way — or null where it turns on them. */
    static Boolean settled(Holding holding) {
        return switch (holding) {
            case null -> null;
            case Holding.AllOf(var ways) -> {
                boolean turns = false;
                for (Holding way : ways) {
                    Boolean one = settled(way);
                    if (Boolean.FALSE.equals(one)) {
                        yield false;
                    }
                    turns |= one == null;
                }
                yield turns ? null : true;
            }
            case Holding.AnyOf(var ways) -> {
                boolean turns = false;
                for (Holding way : ways) {
                    Boolean one = settled(way);
                    if (Boolean.TRUE.equals(one)) {
                        yield true;
                    }
                    turns |= one == null;
                }
                yield turns ? null : false;
            }
            case Holding.Not(Holding denied) -> {
                Boolean one = settled(denied);
                yield one == null ? null : !one;
            }
            case Holding.Something(LinearForm<FactSubject> count) -> standing(count, Rel.GT);
            case Holding.Stands(LinearForm<FactSubject> form, Rel rel) -> standing(form, rel);
            case Holding.Unnamed _ -> null;
        };
    }

    /** Whether {@code form} stands {@code rel} to nought whatever the counts and numbers are, which
     *  it does one way or the other where it is a constant — or null where it weighs any. */
    private static Boolean standing(LinearForm<FactSubject> form, Rel rel) {
        return form.coefs().isEmpty() ? rel.holds(form.constant().signum()) : null;
    }

    /**
     * The relations {@code holding} coming out {@code positive} makes certain over the counts and
     * numbers, each {@code form rel 0} — or null where it cannot come out that way at all. A
     * disjunction of more than one way that may hold makes nothing certain, and is left out: what is
     * taken is never more than the law says.
     */
    static List<NumericConstraint> certain(Holding holding, boolean positive) {
        List<NumericConstraint> out = new ArrayList<>();
        return certain(holding, positive, out) ? out : null;
    }

    private static boolean certain(Holding holding, boolean positive, List<NumericConstraint> out) {
        return switch (holding) {
            case Holding.Something(LinearForm<FactSubject> count) -> {
                // A count is a whole number, so holding something is holding at least one.
                LinearForm<FactSubject> past = count.minus(LinearForm.constant(ExactRatio.ONE))
                        .orNull();
                if (positive && past != null) {
                    out.add(new NumericConstraint(past, Rel.GE));
                } else if (!positive) {
                    out.add(new NumericConstraint(count, Rel.LE));
                }
                yield true;
            }
            case Holding.Stands(LinearForm<FactSubject> form, Rel rel) -> {
                out.add(new NumericConstraint(form, positive ? rel : rel.denied()));
                yield true;
            }
            case Holding.Not(Holding denied) -> certain(denied, !positive, out);
            // It may come out either way, and either way it says nothing of the numbers.
            case Holding.Unnamed _ -> true;
            // Each of them where all hold, and some one where any does not: the same two, turned.
            case Holding.AllOf(var ways) -> positive ? every(ways, true, out)
                    : oneOf(ways, false, out);
            case Holding.AnyOf(var ways) -> positive ? oneOf(ways, true, out)
                    : every(ways, false, out);
        };
    }

    private static boolean every(List<Holding> ways, boolean positive,
                                 List<NumericConstraint> out) {
        for (Holding way : ways) {
            if (!certain(way, positive, out)) {
                return false;
            }
        }
        return true;
    }

    /** The one of {@code ways} that can come out {@code positive}, where only one can; nothing
     *  where more than one can; and false where none can. */
    private static boolean oneOf(List<Holding> ways, boolean positive,
                                 List<NumericConstraint> out) {
        // One way written twice is one way: `s ++ s` holds something where `s` does.
        SequencedSet<Holding> open = new LinkedHashSet<>();
        for (Holding way : ways) {
            if (!Boolean.valueOf(!positive).equals(settled(way))) {
                open.add(way);
            }
        }
        if (open.isEmpty()) {
            return false;
        }
        return open.size() != 1 || certain(open.getFirst(), positive, out);
    }

    @Override
    public ElementsWrittenOut.Reading<Denotations> elements() {
        return elements;
    }

    @Override
    public ElementsWrittenOut.Stood<Denotations> argument(DeclaredArgument argument) {
        Core given = applied.argument(argument);
        return given == null ? null : new ElementsWrittenOut.Stood<>(given, at);
    }

    @Override
    public Holding settles(LawProposition.Always<DeclaredArgument> always) {
        return always.holds() ? new Holding.AllOf(List.of()) : new Holding.AnyOf(List.of());
    }

    @Override
    public Holding joins(LawProposition.All<DeclaredArgument> all, List<Holding> each) {
        return new Holding.AllOf(each);
    }

    @Override
    public Holding eitherOf(LawProposition.Any<DeclaredArgument> any,
                           Function<LawProposition<DeclaredArgument>, Holding> part) {
        List<Holding> each = new ArrayList<>(any.parts().size());
        for (LawProposition<DeclaredArgument> one : any.parts()) {
            each.add(part.apply(one));
        }
        return new Holding.AnyOf(each);
    }

    /** An argument holding something, by how many it holds; nothing else an argument comes out as
     *  is a count. */
    @Override
    public Holding observed(LawProposition.Observed<DeclaredArgument> observed) {
        if (!(observed.of() instanceof LawSubject.Argument<DeclaredArgument>(DeclaredArgument which))
                || observed.side().aspect() != AnswerAspect.EMPTINESS) {
            return new Holding.Unnamed(observed);
        }
        FactSubject count = countOf(applied.argument(which));
        if (count == null) {
            return new Holding.Unnamed(observed);
        }
        Holding something = new Holding.Something(LinearForm.atom(count));
        return observed.side().holds() ? something : new Holding.Not(something);
    }

    @Override
    public Holding compared(LawProposition.Compared<DeclaredArgument> compared) {
        LinearForm<FactSubject> form = form(compared.form());
        return form == null ? new Holding.Unnamed(compared)
                : new Holding.Stands(form, compared.states());
    }

    /**
     * Some element of a container no walk writes out meeting a statement, by how many of its
     * elements meet it ({@link #howManyMeet}) being above nought.
     */
    @Override
    public Holding someElement(LawProposition.SomeElement<DeclaredArgument> some) {
        LinearForm<FactSubject> count = LawAtACall.number(
                new LawNumber.HowManyMeet<>(some.container(), some.ofTheElement()), this);
        if (count == null) {
            return new Holding.Unnamed(some);
        }
        Holding something = new Holding.Something(count);
        return some.holds() ? something : new Holding.Not(something);
    }

    /** What of {@code container} a value is held as, as {@code of} says: one of its elements, or
     *  one of its keys. */
    private static LawSubject<DeclaredArgument> heldAs(DeclaredArgument container,
                                                       AddsWhatItDoesNotHold.Of of) {
        return switch (of) {
            case ELEMENTS -> new LawSubject.ElementOf<>(container);
            case KEYS -> new LawSubject.KeyOf<>(container);
        };
    }

    /** The argument {@code subject} is, or null where it is no argument. */
    private static DeclaredArgument argumentIn(LawSubject<DeclaredArgument> subject) {
        return subject instanceof LawSubject.Argument<DeclaredArgument>(DeclaredArgument at)
                ? at : null;
    }

    @Override
    public Holding writtenOut(LawProposition.SomeElement<DeclaredArgument> some,
                              boolean someMeets) {
        return settles(new LawProposition.Always<>(some.holds() == someMeets));
    }

    /**
     * Two values being one, outside an element counted: a part unnamed. Two values of any type are
     * no relation between numbers, and no law of the library states it of two arguments — it
     * states it of an element and what the element is asked to be, which is a count
     * ({@link #howManyMeet}).
     */
    @Override
    public Holding same(LawProposition.Same<DeclaredArgument> same) {
        return new Holding.Unnamed(same);
    }

    /**
     * One string standing inside another where the law says: a part unnamed, and the one inside
     * holding no more code points than the one around it, where both are strings this names a
     * length of. Where it does not stand inside, either.
     */
    @Override
    public Holding inside(LawProposition.Inside<DeclaredArgument> inside) {
        LawProposition.Inside<DeclaredArgument> standing = new LawProposition.Inside<>(
                inside.inner(), inside.outer(), inside.where(), true);
        Holding unnamed = new Holding.Unnamed(standing);
        FactSubject within = lengthOf(standing.inner());
        FactSubject around = lengthOf(standing.outer());
        Holding holds = within == null || around == null ? unnamed
                : new Holding.AllOf(List.of(unnamed,
                        new Holding.Stands(LinearForm.difference(within, around), Rel.LE)));
        return inside.holds() ? holds : new Holding.Not(holds);
    }

    /** How many code points the argument {@code subject} names holds, or null where it names no
     *  argument or this names no count of it. */
    private FactSubject lengthOf(LawSubject<DeclaredArgument> subject) {
        DeclaredArgument which = argumentIn(subject);
        return which == null ? null : countOf(applied.argument(which));
    }

    /**
     * The size of an argument, by the count its type is counted by; an argument that is a number;
     * how many elements of an argument meet a statement ({@link #howManyMeet}); how many different
     * values they come to; how many they hold added up; and how many code points of a string are
     * in a class — each counted by an atom of what it counts. A size of anything but an argument
     * is no number of the call outside the element it is of.
     */
    @Override
    public LinearForm<FactSubject> counted(LawNumber<DeclaredArgument> number) {
        return switch (number) {
            case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument which) -> {
                Core given = applied.argument(which);
                yield given == null ? null : terms.affineOf(given, at);
            }
            case LawNumber.SizeOf<DeclaredArgument>(
                    LawSubject.Argument<DeclaredArgument>(DeclaredArgument which)) -> {
                FactSubject count = countOf(applied.argument(which));
                yield count == null ? null : LinearForm.atom(count);
            }
            case LawNumber.HowManyMeet<DeclaredArgument> meet -> howManyMeet(meet);
            case LawNumber.HowManyDifferent<DeclaredArgument> different -> atom(different(different));
            case LawNumber.SumOver<DeclaredArgument> sum -> sumOver(sum);
            case LawNumber.CodePointsOf<DeclaredArgument>(var of, var counted) -> {
                DeclaredArgument which = argumentIn(of);
                Core string = which == null ? null : applied.argument(which);
                yield atom(string == null ? null : terms.codePointsAtomFor(string, counted, at));
            }
            case LawNumber.SizeOf<DeclaredArgument> _ -> null;
        };
    }

    private static LinearForm<FactSubject> atom(FactSubject atom) {
        return atom == null ? null : LinearForm.atom(atom);
    }

    /**
     * How many elements of {@code meet}'s container meet what it states.
     *
     * <p>Where it states that something does not hold, how many there are less how many it does
     * hold of. Otherwise how many are an argument, or have a key that is one
     * ({@link Terms#howManyAreAtomFor}); how many some element of another argument is, or whose key
     * some key of it is ({@link #heldOf}); and how many come out on a side, themselves or what a
     * closure answers of each ({@link Terms#howManyMeetFor}). Null where it states anything
     * else.
     */
    private LinearForm<FactSubject> howManyMeet(LawNumber.HowManyMeet<DeclaredArgument> meet) {
        LawProposition<DeclaredArgument> asked = meet.ofTheElement();
        Core container = applied.argument(meet.container());
        if (container == null) {
            return null;
        }
        if (statesAFailing(asked)) {
            FactSubject all = countOf(container);
            LinearForm<FactSubject> meeting = all == null ? null
                    : howManyMeet(new LawNumber.HowManyMeet<>(meet.container(), asked.denied()));
            return meeting == null ? null : LinearForm.atom(all).minus(meeting).orNull();
        }
        return switch (asked) {
            case LawProposition.Same<DeclaredArgument>(var one, var other, boolean _) ->
                    atom(areAnArgument(meet.container(), container, one, other));
            case LawProposition.SomeElement<DeclaredArgument> _ -> heldOf(meet);
            case LawProposition.Observed<DeclaredArgument>(var of, var side) ->
                    comingOut(meet.container(), container, of, side.aspect());
            default -> null;
        };
    }

    /** How many elements of {@code container}, the argument {@code named}, come out on the holding
     *  side of {@code aspect} — each itself, or what a closure answers of each, as {@code of}
     *  says — or null where {@code of} is anything else. */
    private LinearForm<FactSubject> comingOut(DeclaredArgument named, Core container,
                                              LawSubject<DeclaredArgument> of,
                                              AnswerAspect aspect) {
        return switch (of) {
            case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument element)
                    when element.equals(named) ->
                    terms.howManyMeetFor(container, null, aspect, at);
            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument closure) -> {
                Core given = applied.argument(closure);
                yield given == null ? null : terms.howManyMeetFor(container, given, aspect, at);
            }
            default -> null;
        };
    }

    /** Whether {@code asked} states that something does not hold, so that what meets it is what
     *  fails its denial. */
    private static boolean statesAFailing(LawProposition<DeclaredArgument> asked) {
        return switch (asked) {
            case LawProposition.Same<DeclaredArgument> same -> !same.holds();
            case LawProposition.SomeElement<DeclaredArgument> some -> !some.holds();
            case LawProposition.Observed<DeclaredArgument> observed -> !observed.side().holds();
            case LawProposition.Inside<DeclaredArgument> inside -> !inside.holds();
            default -> false;
        };
    }

    /** How many elements of {@code container}, the argument {@code named}, are an argument — or
     *  have a key that is one — where {@code one} and {@code other} are the element or its key and
     *  that argument, either way round. */
    private FactSubject areAnArgument(DeclaredArgument named, Core container,
                                      LawSubject<DeclaredArgument> one,
                                      LawSubject<DeclaredArgument> other) {
        for (AddsWhatItDoesNotHold.Of of : AddsWhatItDoesNotHold.Of.values()) {
            LawSubject<DeclaredArgument> held = heldAs(named, of);
            DeclaredArgument value = held.equals(one) ? argumentIn(other)
                    : held.equals(other) ? argumentIn(one) : null;
            Core given = value == null ? null : applied.argument(value);
            FactSubject count = given == null ? null
                    : terms.howManyAreAtomFor(container, given, of, at);
            if (count != null) {
                return count;
            }
        }
        return null;
    }

    /** How many different values {@code different} counts over its container: its elements, their
     *  keys, or what a closure answers of each — or null where it counts anything else. */
    private FactSubject different(LawNumber.HowManyDifferent<DeclaredArgument> different) {
        Core container = applied.argument(different.container());
        if (container == null) {
            return null;
        }
        return switch (different.ofTheElement()) {
            case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument of)
                    when of.equals(different.container()) -> terms.howManyDifferentAtomFor(
                    container, null, AddsWhatItDoesNotHold.Of.ELEMENTS, at);
            case LawSubject.KeyOf<DeclaredArgument>(DeclaredArgument of)
                    when of.equals(different.container()) -> terms.howManyDifferentAtomFor(
                    container, null, AddsWhatItDoesNotHold.Of.KEYS, at);
            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument closure) -> {
                Core given = applied.argument(closure);
                yield given == null ? null : terms.howManyDifferentAtomFor(container, given,
                        AddsWhatItDoesNotHold.Of.ELEMENTS, at);
            }
            default -> null;
        };
    }

    /**
     * How many the elements of {@code sum}'s container hold, added up — each element or what a
     * closure answers of each — or null where it adds up any other number.
     *
     * <p>Where the container is written out, the sizes of what it was written with, each read where
     * it stands ({@link LawAtACall#sizedOfEachWrittenOut}); otherwise the atom of the sum.
     */
    private LinearForm<FactSubject> sumOver(LawNumber.SumOver<DeclaredArgument> sum) {
        Core container = applied.argument(sum.container());
        if (container == null
                || !(sum.ofTheElement() instanceof LawNumber.SizeOf<DeclaredArgument>(var of))) {
            return null;
        }
        List<ElementsWrittenOut.Stood<Denotations>> each =
                LawAtACall.sizedOfEachWrittenOut(sum, this);
        if (each != null) {
            LinearForm<FactSubject> total = LinearForm.constant(ExactRatio.ZERO);
            for (ElementsWrittenOut.Stood<Denotations> one : each) {
                FactSubject holds = terms.sizeOfWhatItHolds(one.value(), one.at());
                total = holds == null ? null : total.plus(LinearForm.atom(holds)).orNull();
                if (total == null) {
                    return null;
                }
            }
            return total;
        }
        return atom(switch (of) {
            case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument element)
                    when element.equals(sum.container()) ->
                    terms.sumOfSizesAtomFor(container, null, at);
            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument closure) -> {
                Core given = applied.argument(closure);
                yield given == null ? null : terms.sumOfSizesAtomFor(container, given, at);
            }
            default -> null;
        });
    }

    @Override
    public LinearForm<FactSubject> writtenOut(LawNumber.HowManyMeet<DeclaredArgument> number,
                                              long many) {
        return LinearForm.constant(ExactRatio.of(many));
    }

    /**
     * How many elements of one argument another holds ({@link Terms#howManyAreInAtomFor}), where
     * {@code meet} counts the elements some element of the other is, or those whose key some key
     * of the other is. Null where it counts anything else.
     */
    private LinearForm<FactSubject> heldOf(LawNumber.HowManyMeet<DeclaredArgument> meet) {
        if (!(meet.ofTheElement() instanceof LawProposition.SomeElement<DeclaredArgument>(
                DeclaredArgument holder, LawProposition.Same<DeclaredArgument>(
                        var one, var other, boolean same), boolean some))
                || !same || !some) {
            return null;
        }
        Core counted = applied.argument(meet.container());
        Core holding = applied.argument(holder);
        for (AddsWhatItDoesNotHold.Of of : AddsWhatItDoesNotHold.Of.values()) {
            LawSubject<DeclaredArgument> ofCounted = heldAs(meet.container(), of);
            LawSubject<DeclaredArgument> ofHolder = heldAs(holder, of);
            boolean alike = (one.equals(ofCounted) && other.equals(ofHolder))
                    || (one.equals(ofHolder) && other.equals(ofCounted));
            FactSubject held = !alike || counted == null || holding == null ? null
                    : terms.howManyAreInAtomFor(counted, holding, of, at);
            if (held != null) {
                return LinearForm.atom(held);
            }
        }
        return null;
    }

    /** {@code form}, over numbers of the arguments, as a form over the atoms each is — or null
     *  where one of them is none, or the sum has no representation. */
    private LinearForm<FactSubject> form(LinearForm<LawNumber<DeclaredArgument>> form) {
        return form.over(number -> LawAtACall.number(number, this));
    }

    /** The count of what {@code argument} is, by the measure its type is counted by, or null where
     *  there is no argument there, nothing counts it, or this cannot name the count. */
    private FactSubject countOf(Core argument) {
        if (argument == null) {
            return null;
        }
        ValueName counts = NumericMeasures.takenOf(Core.withoutStanding(argument).type(),
                terms.newtypeInners());
        return counts == null ? null : terms.sizeAtomFor(counts, argument, at);
    }
}
