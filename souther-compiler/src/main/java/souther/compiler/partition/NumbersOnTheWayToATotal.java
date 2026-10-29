package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ObservationSource;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.HashSet;
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
 * <p>Anything else is not shown here, which is not that it stops.
 */
final class NumbersOnTheWayToATotal {

    private NumbersOnTheWayToATotal() {
    }

    /**
     * Whether working {@code node} out, which comes to {@code answer}, works out nothing beyond
     * the type where {@code answer} is in it: by what its own operations refuse
     * ({@link WhatARunMayEndFor#endsOnlyWhereItsAnswerHasNoPlace}), or because every number on
     * the way lies between nought and the answer.
     */
    static boolean completeWhereTheAnswerHasAPlace(Core node, LinearForm<NumericTerm> answer,
                                                   InputReading read) {
        return WhatARunMayEndFor.endsOnlyWhereItsAnswerHasNoPlace(node)
                || (betweenNoughtAndTheAnswer(node, true) && noughtOrMoreFromEachElement(answer,
                read));
    }

    /**
     * Whether what {@code e} works out outside the closures written at it ends no run, but for
     * the operation at the top that refuses only an answer with no place; and every function it
     * applies is a closure written under it that works out only numbers between nought and what
     * it answers.
     */
    private static boolean betweenNoughtAndTheAnswer(Core e, boolean top) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Block closure) {
            Set<BindingId> handed = new HashSet<>();
            for (Core.Binder param : closure.params()) {
                if (param == null || param.binding() == null) {
                    return false;
                }
                handed.add(param.binding());
            }
            return closure.body().type() == Type.INT
                    && noMoreThanItAnswers(closure.body(), handed, new HashSet<>());
        }
        // A call handed a function any other way is answered whole, the function's body with it.
        if (!(WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(here)
                instanceof WhatARunMayEndFor.Endings.Known own)
                || !own.kinds().kinds().stream().allMatch(kind -> top
                        && kind == AbortKind.REQUIRED_FORM_HAS_NO_PLACE)) {
            return false;
        }
        boolean[] under = {true};
        Core.forEachChild(here, child -> under[0] &= betweenNoughtAndTheAnswer(child, false));
        return under[0];
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
