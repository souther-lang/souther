package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.check.CallArguments;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ObservationSource;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Whether every number a total works out on the way lies between nought and the total, so that
 * working it out completes wherever the total is an {@code Int}.
 *
 * <p>A total over a container whose length is not known applies a closure once per element, and a
 * walk from a seed applies its step once per element, each with operations of its own. Where those
 * cannot be listed, what is shown of them is one statement about an arbitrary application. This is
 * the statement: what each element contributes is at least nought, the seed is at least nought,
 * and every operation an application works out is an addition, or a product by a written number
 * of at least one, of numbers at least nought. Each number such an application works out is then
 * at least nought and no more than what the application answers, and each answer so far of a walk
 * no more than the next; so every number worked out lies between nought and the total, and none
 * passes the type where the total does not.
 *
 * <p>Only of an application whose answer is added into the total: the walk's step, or a closure
 * whose answers are the elements the total adds up. A closure whose answer is put to another use
 * is no less than nought and no more than nothing the total holds; a key {@code List.sortBy}
 * orders by passes the type where the total of what it orders does not, and so does a closure
 * whose answers {@code List.length} only counts.
 *
 * <p>Anything else is not shown here, which is not that it stops.
 */
final class NumbersOnTheWayToATotal {

    private NumbersOnTheWayToATotal() {
    }

    /**
     * Whether working {@code node} out here, which comes to {@code answer}, works out nothing
     * beyond the type where {@code answer} is in it, and nor does working out what each name it
     * reads was given ({@link InputReads#boundTo}): a reading of the input follows a name to the
     * value it was given, and that value is worked out whatever the name goes on to stand as.
     */
    static boolean completeWhereTheAnswerHasAPlace(Core node, LinearForm<NumericTerm> answer,
                                                   InputReading read, InputReads at) {
        if (workedOutWhereItsAnswerHasAPlace(node)
                && soIsWhatEachNameWasGiven(node, read, at, new HashSet<>())) {
            return true;
        }
        Set<BindingId> addedIn = new HashSet<>();
        return noughtOrMoreFromEachElement(answer, read)
                && addsUpWhatItsClosuresAnswer(node, read, at, addedIn)
                && soIsWhatEachNameWasGiven(node, read, at, addedIn);
    }

    /**
     * Whether working {@code e} out works out nothing beyond the type where what it answers is in
     * it: it applies no function, so every number on the way is the answer of a part of it and the
     * numbers of the input it is read as stand only where each part has one; or what its own
     * operations refuse ({@link WhatARunMayEndFor#endsOnlyWhereItsAnswerHasNoPlace}) is all it
     * refuses.
     */
    private static boolean workedOutWhereItsAnswerHasAPlace(Core e) {
        return !appliesAFunction(e) || WhatARunMayEndFor.endsOnlyWhereItsAnswerHasNoPlace(e);
    }

    /** Whether what each name read under {@code e} was given is worked out where its answer has
     *  a place, each name followed once and none in {@code followed} again. */
    private static boolean soIsWhatEachNameWasGiven(Core e, InputReading read, InputReads at,
                                                    Set<BindingId> followed) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Read name && followed.add(name.binding())) {
            for (Denotation given : at.boundTo(here, read.rules().symbols(),
                    read.rules().newtypes())) {
                if (!workedOutWhereItsAnswerHasAPlace(given.value())
                        || !soIsWhatEachNameWasGiven(given.value(), read, given.at(), followed)) {
                    return false;
                }
            }
        }
        boolean[] so = {true};
        Core.forEachChild(here, child -> so[0] = so[0]
                && soIsWhatEachNameWasGiven(child, read, at, followed));
        return so[0];
    }

    /**
     * Whether {@code e} adds up a container, as a total of it or as a walk whose step adds to the
     * answer so far, and every closure applied on the way answers what is added in: the step, or
     * a closure each element of the container is the answer of
     * ({@link BuiltFrom#mapsEachElementOf}), down a run of those. Each number such a closure works
     * out is then no more than an addend of the answer. A closure whose answer is put to any other
     * use — a key to sort by, a condition, something only counted — adds nothing in, and what it
     * works out is not between nought and the answer.
     *
     * <p>The names the run of containers is read through are followed to what they were given and
     * put in {@code addedIn}: what each was given is asked here.
     */
    private static boolean addsUpWhatItsClosuresAnswer(Core e, InputReading read, InputReads at,
                                                       Set<BindingId> addedIn) {
        Core here = Core.withoutStanding(e);
        SeededWalk walk = SeededWalk.of(here, NumbersOnTheWayToATotal::writtenClosure);
        if (walk != null) {
            // The elements are added in only where the step reads the one it is handed.
            Set<BindingId> readByTheStep = new HashSet<>();
            return WhatARunMayEndFor.endsNoneBeneath(walk.seed())
                    && answersNoMoreThanItIsHanded(walk.step(), readByTheStep)
                    && madeOfWhatClosuresAnswer(walk.container(),
                            readByTheStep.contains(walk.element().binding()), read, at, addedIn);
        }
        if (!(here instanceof Core.PreservedCall call)
                || !(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(call)
                        instanceof GetsPast.WhereTheTotalFits(int container))
                || container >= call.args().size()) {
            return false;
        }
        for (int i = 0; i < call.args().size(); i++) {
            if (i != container && !WhatARunMayEndFor.endsNoneBeneath(call.args().get(i))) {
                return false;
            }
        }
        return madeOfWhatClosuresAnswer(call.args().get(container), true, read, at, addedIn);
    }

    /**
     * Whether the elements of {@code e} are each what a closure answered, where they are
     * {@code addedIn} to the answer, down a run of calls that hold one closure answer for each
     * element of a container ({@link BuiltFrom#mapsEachElementOf}) and end no run apart from the
     * closure, each closure answering no more than it is handed; or {@code e} applies no function
     * and ends no run. A name is followed to what it was given.
     */
    private static boolean madeOfWhatClosuresAnswer(Core e, boolean addedIn, InputReading read,
                                                    InputReads at, Set<BindingId> followed) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Read name) {
            List<Denotation> given = at.boundTo(here, read.rules().symbols(),
                    read.rules().newtypes());
            if (given.isEmpty()) {
                return true;
            }
            followed.add(name.binding());
            return given.stream().allMatch(each -> madeOfWhatClosuresAnswer(each.value(),
                    addedIn, read, each.at(), followed));
        }
        if (addedIn && here instanceof Core.PreservedCall call) {
            BuiltFrom<DeclaredArgument> built =
                    DefaultBoundOperationFacts.get().buildsItsResultFrom(call.operation());
            DeclaredArgument mapped = built == null ? null : built.mapsEachElementOf();
            int over = mapped == null ? -1 : CallArguments.positionOf(mapped, call.operation());
            if (over >= 0 && over < call.args().size()
                    && WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(call).endsNone()) {
                Core.Block closure = null;
                for (int i = 0; i < call.args().size(); i++) {
                    Core.Block block = i == over ? null : writtenClosure(call.args().get(i));
                    if (block != null) {
                        if (closure != null) {
                            return false;
                        }
                        closure = block;
                    } else if (i != over
                            && !WhatARunMayEndFor.endsNoneBeneath(call.args().get(i))) {
                        return false;
                    }
                }
                return closure != null && answersNoMoreThanItIsHanded(closure, new HashSet<>())
                        && madeOfWhatClosuresAnswer(call.args().get(over), true, read, at,
                        followed);
            }
        }
        return !appliesAFunction(here) && WhatARunMayEndFor.endsNoneBeneath(here);
    }

    /** The closure {@code e} is written as, or null where it is none. */
    private static Core.Block writtenClosure(Core e) {
        return Core.withoutStanding(e) instanceof Core.Block block ? block : null;
    }

    /**
     * Whether every number {@code closure} works out is at least nought and no more than what it
     * answers, given that what it is handed is at least nought ({@link #noMoreThanItAnswers});
     * each parameter it reads is put in {@code read}.
     */
    private static boolean answersNoMoreThanItIsHanded(Core.Block closure,
                                                       Set<BindingId> read) {
        Set<BindingId> handed = new HashSet<>();
        for (Core.Binder param : closure.params()) {
            if (param == null || param.binding() == null) {
                return false;
            }
            handed.add(param.binding());
        }
        return closure.body().type() == Type.INT
                && noMoreThanItAnswers(closure.body(), handed, read);
    }

    /** Whether working {@code e} out applies a function: a closure written under it, which what
     *  it is handed to applies as often as it does with numbers of its own on the way, or a
     *  function value applied. A function handed by its name is written at the call as a
     *  closure. */
    private static boolean appliesAFunction(Core e) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Block || here instanceof Core.Apply) {
            return true;
        }
        boolean[] applies = {false};
        Core.forEachChild(here, child -> applies[0] |= appliesAFunction(child));
        return applies[0];
    }

    /**
     * Whether every number {@code e} works out is at least nought and no more than what it
     * answers: additions, and products by a written number of at least one, of a written number
     * of at least nought or of what the closure is handed. What it is handed is at least nought
     * as the caller shows of the elements and the seed. Every part is worked out on every run
     * and adds into the answer, so each name {@code e} reads, put in {@code read}, is no more
     * than the answer either.
     *
     * <p>A value a binding gives a name is worked out before the body whether or not the body
     * reads the name, and is no more than the answer only where the body reads it: the body adds
     * it in at least once. One the body never reads may be any number, and is not shown.
     */
    private static boolean noMoreThanItAnswers(Core e, Set<BindingId> handed,
                                               Set<BindingId> read) {
        return switch (Core.withoutStanding(e)) {
            case Core.Binary sum when sum.op() == BinOp.ADD && sum.type() == Type.INT ->
                    noMoreThanItAnswers(sum.left(), handed, read)
                            && noMoreThanItAnswers(sum.right(), handed, read);
            case Core.Binary product when product.op() == BinOp.MUL
                    && product.type() == Type.INT -> atLeastOne(product.left())
                    ? noMoreThanItAnswers(product.right(), handed, read)
                    : atLeastOne(product.right())
                            && noMoreThanItAnswers(product.left(), handed, read);
            case Core.Int written -> written.value() >= 0;
            case Core.LetIn binding -> {
                BindingId bound = binding.binder().binding();
                Set<BindingId> named = new HashSet<>(handed);
                named.add(bound);
                Set<BindingId> readInTheBody = new HashSet<>();
                boolean shown = noMoreThanItAnswers(binding.value(), handed, read)
                        && noMoreThanItAnswers(binding.body(), named, readInTheBody)
                        && readInTheBody.contains(bound);
                read.addAll(readInTheBody);
                yield shown;
            }
            case Core.Read name -> readOffWhatItIsHanded(name, handed, read);
            case Core.FieldAccess access -> readOffWhatItIsHanded(access, handed, read);
            case Core.FieldProjection projection -> readOffWhatItIsHanded(projection, handed, read);
            default -> false;
        };
    }

    /** Whether {@code e} is a name the closure is handed, or a field read off one, with nothing
     *  worked out on the way; the name is put in {@code read}. */
    private static boolean readOffWhatItIsHanded(Core e, Set<BindingId> handed,
                                                 Set<BindingId> read) {
        Core at = Core.withoutStanding(e);
        while (true) {
            switch (at) {
                case Core.Read name -> {
                    read.add(name.binding());
                    return handed.contains(name.binding());
                }
                case Core.FieldAccess access -> at = Core.withoutStanding(access.target());
                case Core.FieldProjection projection -> at = Core.withoutStanding(projection.base());
                default -> {
                    return false;
                }
            }
        }
    }

    private static boolean atLeastOne(Core e) {
        return Core.withoutStanding(e) instanceof Core.Int written && written.value() >= 1;
    }

    /**
     * Whether {@code answer} is at least nought made of what each element contributes, and each
     * element contributes at least nought: a seed of at least nought, and counts and totals each
     * weighed by at least nought, of elements whose places the rules hold at nought or more.
     */
    private static boolean noughtOrMoreFromEachElement(LinearForm<NumericTerm> answer,
                                                       InputReading read) {
        if (answer.constant().signum() < 0) {
            return false;
        }
        for (Map.Entry<NumericTerm, ExactRatio> each : answer.coefs().entrySet()) {
            if (each.getValue().signum() < 0 || !eachElementAtLeastNought(each.getKey(), read)) {
                return false;
            }
        }
        return true;
    }

    private static boolean eachElementAtLeastNought(NumericTerm term, InputReading read) {
        return switch (term) {
            case NumericTerm.TakenOf taken -> switch (taken.takenAs()) {
                case TakenAs.HowManyItHolds _ -> true;
                case TakenAs.TheSumOfWhatItHolds _ -> taken.source().equals(
                        ObservationSource.asItStands(taken.position()))
                        && atLeastNought(taken.position().element(), read);
                default -> false;
            };
            case NumericTerm.TakenOver over -> switch (over.takenAs()) {
                case TakenAs.HowManyItHolds _ -> true;
                case TakenAs.TheSumOfWhatItHolds _ -> switch (over.source()) {
                    case RunSource.ProjectedOccurrences projected ->
                            atLeastNought(projected.subjectPath(), read);
                    case RunSource.ComputedOccurrences computed ->
                            computed.computation() instanceof ElementValue.Affine affine
                                    && affine.form().constant().signum() >= 0
                                    && affine.form().coefs().entrySet().stream().allMatch(
                                            weighed -> weighed.getValue().signum() >= 0
                                                    && atLeastNought(weighed.getKey()
                                                    .from(computed.elements()), read));
                    default -> false;
                };
                default -> false;
            };
            default -> false;
        };
    }

    /** Whether the rules hold every value at {@code place} at nought or more. */
    private static boolean atLeastNought(TermPath place, InputReading read) {
        NumericDomain.Bounds bounds =
                read.quantities().runsBetween(new NumericTerm.ValueOf(place));
        return bounds != null && bounds.min() != null
                && bounds.min().at() instanceof Count(var least) && least.signum() >= 0;
    }
}
