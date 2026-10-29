package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

/**
 * What a run has worked out once it has the value of an expression: the expression's own parts,
 * as {@link Evaluated#inOrder} has them and every arm of a branch, and what each name read in it
 * was given ({@link InputReads#boundTo}), where it was given.
 *
 * <p>The one place this is followed. Whether working something out may end a run before a row
 * of a comparison gets past it is a question about all of it: a name stands for a value worked
 * out where it was bound, and a run reaches the read only through that. What a node does each
 * time it is worked out, apart from the values it reads by name, is the other question, and
 * {@link WhatARunMayEndFor} answers that.
 *
 * <p>What a node itself may end a run for, apart from its parts and the names it reads, is
 * {@code itself}'s to say: {@link WhatARunMayEndFor#itself} where nothing knows more, and a
 * reading that knows a construction's invariant or a called behavior's body says it there.
 */
final class WorkedOutToReachIt {

    private final InputReading read;
    private final Predicate<Denotation> itself;
    /** Whether a call is asked apart from the closures written at it, each closure's body then
     *  being worked out as part of the call that applies it; otherwise a closure is a value made
     *  and the call that applies it answers for its body. */
    private final boolean closuresApart;

    private WorkedOutToReachIt(InputReading read, Predicate<Denotation> itself,
                               boolean closuresApart) {
        this.read = Objects.requireNonNull(read);
        this.itself = Objects.requireNonNull(itself);
        this.closuresApart = closuresApart;
    }

    /**
     * What a run works out to reach a value, each node asked of {@link WhatARunMayEndFor} apart
     * from the closures written at it ({@link WhatARunMayEndFor#itselfApartFromTheClosuresWrittenAtIt}),
     * and the body of each such closure worked out with the call.
     */
    static WorkedOutToReachIt of(InputReading read) {
        return new WorkedOutToReachIt(read,
                value -> WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(value.value())
                        .endsNone(), true);
    }

    /** The same, each node asked of {@code itself} with whatever it applies. */
    static WorkedOutToReachIt asking(InputReading read, Predicate<Denotation> itself) {
        return new WorkedOutToReachIt(read, itself, false);
    }

    /**
     * The same, for a number of the input that stands for {@code shifts}, each a shift of a date
     * the number is defined only where it leaves a date
     * ({@link InputNumber#theShiftsATakingOfItStandsFor}): wherever the number has a value, each
     * of them got there, though it ends a run where its answer has no place.
     */
    WorkedOutToReachIt whereANumberStandsFor(List<Core> shifts) {
        if (shifts.isEmpty()) {
            return this;
        }
        Set<Core> standsFor = Collections.newSetFromMap(new IdentityHashMap<>());
        standsFor.addAll(shifts);
        Predicate<Denotation> before = itself;
        return new WorkedOutToReachIt(read, value -> before.test(value)
                || (standsFor.contains(Core.withoutStanding(value.value()))
                        && endsOnlyWhereItsOwnAnswerHasNoPlace(
                                Core.withoutStanding(value.value()))),
                closuresApart);
    }

    private boolean endsOnlyWhereItsOwnAnswerHasNoPlace(Core written) {
        WhatARunMayEndFor.Endings own = closuresApart
                ? WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(written)
                : WhatARunMayEndFor.itself(written);
        return own instanceof WhatARunMayEndFor.Endings.Known(var kinds)
                && kinds.kinds().stream()
                        .allMatch(kind -> kind == AbortKind.REQUIRED_FORM_HAS_NO_PLACE);
    }

    /** Whether working out {@code value}, and what each name read in it was given, ends no run. */
    boolean endsNoRun(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        if (closuresApart && written instanceof Core.Block closure) {
            return endsNoRun(new Denotation(closure.body(), value.at()));
        }
        if (written instanceof Core.LetIn let) {
            return endsNoRun(new Denotation(let.value(), value.at()))
                    && endsNoRun(new Denotation(let.body(),
                            value.at().and(let.binder(), let.value())));
        }
        // Written in a value that was built, whatever is inside it: the build ran all of it.
        if (written instanceof Core.Construct made && read.rules().declarations().answers()
                .builtWhereItsModuleIsBuilt(read.rules().symbols().module(), made.pos())) {
            return true;
        }
        // A reference to a value is run as the value is defined, which no part of this node says.
        if (written instanceof Core.MaterialisedValue) {
            Denotation defined = value.at().taken(written);
            return defined != null && endsNoRun(defined);
        }
        // An operator over numbers the same on every run is worked out where it is folded, by the
        // arithmetic the run time does: one that aborts there folds to nothing.
        if (closuresApart && (written instanceof Core.Binary || written instanceof Core.Neg)
                && value.at().folded(written, read.rules().symbols(), read.rules().newtypes())
                        .isPresent()) {
            return true;
        }
        return itself.test(value) && partsAndNamesEndNoRun(value);
    }

    /**
     * Whether working out {@code value} gets there wherever its own answer has a place: it ends a
     * run itself only where its answer has none, which a row standing at a value of that answer
     * is not at, and nothing it is made of or reads by name ends one at all.
     *
     * <p>Only the answer the row stands at is answered for by where it stands. That a part's
     * answer has a place is no consequence of the whole's having one: a total of {@code 2 * n}
     * and {@code -n} is {@code n}, which has a place where {@code 2 * n} does not. An owner that
     * shows a part gets there wherever the whole does shows it on its own account
     * ({@link NumbersOnTheWayToATotal}).
     */
    boolean endsOnlyWhereItsAnswerHasNoPlace(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        if (written instanceof Core.LetIn let) {
            return endsNoRun(new Denotation(let.value(), value.at()))
                    && endsOnlyWhereItsAnswerHasNoPlace(new Denotation(let.body(),
                            value.at().and(let.binder(), let.value())));
        }
        return endsOnlyWhereItsOwnAnswerHasNoPlace(written) && partsAndNamesEndNoRun(value);
    }

    private boolean partsAndNamesEndNoRun(Denotation value) {
        for (Core part : whatIsRunWith(Core.withoutStanding(value.value()))) {
            if (!endsNoRun(new Denotation(part, value.at()))) {
                return false;
            }
        }
        for (Denotation bound : boundTo(value)) {
            if (!endsNoRun(bound)) {
                return false;
            }
        }
        return true;
    }

    /** What the name {@code value} is was given, where it was given; none where it is no name
     *  given a value, a position of the input or what an application was handed. */
    List<Denotation> boundTo(Denotation value) {
        return value.at().boundTo(value.value(), read.rules().symbols(), read.rules().newtypes());
    }

    /**
     * The parts of {@code written} whose ending a run is the ending of a run of it: what
     * {@link Evaluated#inOrder} says is evaluated, and every branch and arm, which are not
     * evaluated by reaching the node but one of which is, so that all of them are asked.
     *
     * <p>A function value is made and not run where it is written, so its body is not a part. The
     * construction an {@code if} tests for is a part by its fields alone: a refusal of its
     * invariant is the branch the {@code if} takes and ends nothing.
     */
    static List<Core> whatIsRunWith(Core written) {
        List<Core> parts = new ArrayList<>();
        if (Core.withoutStanding(written) instanceof Core.IfConstructed tested) {
            tested.construct().values().forEach(field -> parts.add(field.value()));
            parts.add(tested.then());
            tested.els().forEach(arm -> parts.add(arm.body()));
            return parts;
        }
        for (Evaluated.Step step : Evaluated.inOrder(written)) {
            parts.add(step.expression());
        }
        switch (Core.withoutStanding(written)) {
            case Core.If fork -> {
                parts.add(fork.then());
                parts.add(fork.els());
            }
            case Core.Match match -> match.cases().forEach(arm -> parts.add(arm.body()));
            default -> { }
        }
        return parts;
    }
}
