package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;

/**
 * What a run has worked out once it has the value of an expression: the expression's own parts,
 * as {@link Evaluated#inOrder} has them and every arm of a branch, and what each name read in it
 * was given ({@link souther.compiler.inputs.InputReads#boundTo}), where it was given.
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
        return itself.test(value) && partsAndNamesEndNoRun(value);
    }

    /**
     * Whether working out {@code value} gets there wherever its answer has a place: it ends a
     * run itself only where its own answer has none, which a row standing at a value of the answer
     * is not at, and so does everything on the way to that answer
     * ({@link #onTheWayToTheAnswer}).
     */
    boolean endsOnlyWhereItsAnswerHasNoPlace(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        if (written instanceof Core.LetIn let) {
            return endsNoRun(new Denotation(let.value(), value.at()))
                    && endsOnlyWhereItsAnswerHasNoPlace(new Denotation(let.body(),
                            value.at().and(let.binder(), let.value())));
        }
        return endsOnlyWhereItsOwnAnswerHasNoPlace(written)
                && partsAndNamesAreOnTheWayToTheAnswer(value);
    }

    /**
     * Whether {@code value}, worked out on the way to an answer that has a place, gets there. An
     * operation of the library ends a run only where its own answer has no place, and then the
     * answer made of it has none either: a row standing at a value of that answer is a row where
     * this one had a value. An operator is another thing: its answer is folded into the form the
     * answer is read as, and a run stops at it where the form has a place, so it ends none, or
     * works out only numbers written down. The body of a closure is worked out the same way, as
     * numbers folded into what the call answers, and a function value applied is answered by
     * nothing here.
     */
    private boolean onTheWayToTheAnswer(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        if (closuresApart && written instanceof Core.Block closure) {
            return endsNoRun(new Denotation(closure.body(), value.at()));
        }
        if (written instanceof Core.LetIn || written instanceof Core.Construct
                || written instanceof Core.MaterialisedValue) {
            return endsNoRun(value);
        }
        boolean answers = (written instanceof Core.Binary || written instanceof Core.Neg)
                ? ownEndings(written).endsNone() || readsNoName(written)
                : endsOnlyWhereItsOwnAnswerHasNoPlace(written);
        return answers && partsAndNamesAreOnTheWayToTheAnswer(value);
    }

    private boolean partsAndNamesAreOnTheWayToTheAnswer(Denotation value) {
        for (Core part : whatIsRunWith(Core.withoutStanding(value.value()))) {
            if (!onTheWayToTheAnswer(new Denotation(part, value.at()))) {
                return false;
            }
        }
        for (Denotation bound : boundTo(value)) {
            if (!onTheWayToTheAnswer(bound)) {
                return false;
            }
        }
        return true;
    }

    private boolean endsOnlyWhereItsOwnAnswerHasNoPlace(Core written) {
        return ownEndings(written) instanceof WhatARunMayEndFor.Endings.Known(var kinds)
                && kinds.kinds().stream()
                        .allMatch(kind -> kind == AbortKind.REQUIRED_FORM_HAS_NO_PLACE);
    }

    /** What {@code written} itself may end a run for, apart from the closures written at it
     *  where their bodies are worked out with it. */
    private WhatARunMayEndFor.Endings ownEndings(Core written) {
        return closuresApart ? WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(written)
                : WhatARunMayEndFor.itself(written);
    }

    /** Whether nothing under {@code e} is a name, so that it works out numbers written down. */
    private static boolean readsNoName(Core e) {
        Core here = Core.withoutStanding(e);
        if (here instanceof Core.Read) {
            return false;
        }
        boolean[] none = {true};
        Core.forEachChild(here, child -> none[0] = none[0] && readsNoName(child));
        return none[0];
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
