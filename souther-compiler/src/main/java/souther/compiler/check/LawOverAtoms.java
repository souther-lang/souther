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
import java.util.List;
import java.util.function.Function;

/**
 * What a law of the library says at a call, as the discharge of a rule names it: a statement over
 * the counts and numbers of the arguments ({@link Holding}), and a number as a form over them.
 *
 * <p>The law is taken apart by {@link LawAtACall}, as the reading of an input takes it apart; this
 * answers only the parts that reading leaves to a reader, in the names this side has. A part those
 * names do not reach is null, and a statement with such a part is null as a whole: a law says when
 * something holds and, by the same statement, when it does not, so a part left out would answer the
 * second wrong.
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
     * in {@code at} — or null where no law settles that side, or a part of it is one this cannot
     * name.
     */
    static Holding whereItHolds(AnOperationApplied applied, AnswerAspect aspect, Denotations at,
                                Terms terms) {
        if (applied == null) {
            return null;
        }
        return DefaultBoundOperationFacts.get().settled(applied.operation(),
                OperationLaw.Observed.of(aspect)) instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Observation<DeclaredArgument>(
                                AnswerAspect stated, LawProposition<DeclaredArgument> law),
                        var _) && stated == aspect
                ? LawAtACall.of(law, new LawOverAtoms(applied, at, terms)) : null;
    }

    /**
     * How many {@code applied}'s answer holds as its law says, read in {@code at} — the form the
     * first case it is in comes to, where every case before it is settled as not met and it is
     * settled as met — or null where no law says, or which case it is turns on the run.
     */
    static LinearForm<FactSubject> sizeOf(AnOperationApplied applied, Denotations at,
                                          Terms terms) {
        if (applied == null || !(DefaultBoundOperationFacts.get().settled(applied.operation(),
                OperationLaw.Observed.SIZE) instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw.Size<DeclaredArgument> law, var _))) {
            return null;
        }
        LawOverAtoms reading = new LawOverAtoms(applied, at, terms);
        for (OperationLaw.Size.Case<DeclaredArgument> each : law.cases()) {
            Boolean met = settled(LawAtACall.of(each.where(), reading));
            if (met == null) {
                return null;
            }
            if (met) {
                return reading.form(each.equalTo());
            }
        }
        return null;
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
            case Holding.Something _, Holding.Stands _ -> null;
        };
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
        List<Holding> open = new ArrayList<>();
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
        return each.contains(null) ? null : new Holding.AllOf(each);
    }

    @Override
    public Holding eitherOf(LawProposition.Any<DeclaredArgument> any,
                           Function<LawProposition<DeclaredArgument>, Holding> part) {
        List<Holding> each = new ArrayList<>(any.parts().size());
        for (LawProposition<DeclaredArgument> one : any.parts()) {
            Holding read = part.apply(one);
            if (read == null) {
                return null;
            }
            each.add(read);
        }
        return new Holding.AnyOf(each);
    }

    /** An argument holding something, by how many it holds; nothing else an argument comes out as
     *  is a count. */
    @Override
    public Holding observed(LawProposition.Observed<DeclaredArgument> observed) {
        if (!(observed.of() instanceof LawSubject.Argument<DeclaredArgument>(DeclaredArgument which))
                || observed.side().aspect() != AnswerAspect.EMPTINESS) {
            return null;
        }
        FactSubject count = countOf(applied.argument(which));
        if (count == null) {
            return null;
        }
        Holding something = new Holding.Something(LinearForm.atom(count));
        return observed.side().holds() ? something : new Holding.Not(something);
    }

    @Override
    public Holding compared(LawProposition.Compared<DeclaredArgument> compared) {
        LinearForm<FactSubject> form = form(compared.form());
        return form == null ? null : new Holding.Stands(form, compared.states());
    }

    /** Some element of a container no walk writes out, which no atom here names. */
    @Override
    public Holding someElement(LawProposition.SomeElement<DeclaredArgument> some) {
        return null;
    }

    @Override
    public Holding writtenOut(LawProposition.SomeElement<DeclaredArgument> some,
                              boolean someMeets) {
        return settles(new LawProposition.Always<>(some.holds() == someMeets));
    }

    /** Two values being one, which no relation between numbers says. */
    @Override
    public Holding same(LawProposition.Same<DeclaredArgument> same) {
        return null;
    }

    /** The size of an argument, by the count its type is counted by, and an argument that is a
     *  number; nothing else. */
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
            case LawNumber.SizeOf<DeclaredArgument> _,
                 LawNumber.HowManyMeet<DeclaredArgument> _,
                 LawNumber.HowManyDifferent<DeclaredArgument> _,
                 LawNumber.SumOver<DeclaredArgument> _,
                 LawNumber.CodePointsOf<DeclaredArgument> _ -> null;
        };
    }

    @Override
    public LinearForm<FactSubject> writtenOut(LawNumber.HowManyMeet<DeclaredArgument> number,
                                              long many) {
        return LinearForm.constant(ExactRatio.of(many));
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
