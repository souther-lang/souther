package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.DeclarationMeaning;
import souther.compiler.check.FoldedValue;
import souther.compiler.check.PublishedDeclarationResult;
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
import java.util.Map;
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
 * {@link WhatARunMayEndFor#itself}'s to say, but for a construction, whose invariant is the
 * declaration's ({@link #itselfEndsNoRun}). Where that leaves it unknown, {@code beyond} may know
 * more: a reading that knows a called behavior's body, or a rule that told the node elsewhere.
 */
final class WorkedOutToReachIt {

    private final InputReading read;
    private final Predicate<Denotation> beyond;
    /** Whether a call is asked apart from the closures written at it, each closure's body then
     *  being worked out as part of the call that applies it; otherwise a closure is a value made
     *  and the call that applies it answers for its body. */
    private final boolean closuresApart;
    /** Expressions whose working out another reading told, whole: nothing here asks them. */
    private final Set<Core> toldElsewhere;

    /**
     * One question asked of what a run works out, for as long as it is asked: what each
     * expression met was answered, and what each name a fold met came to.
     *
     * <p>Within one question an expression is worked out where it is written, a name standing for
     * the one value its binding gave it, so an expression reached from every read of a name is
     * answered once. A chain of names each read more than once is otherwise walked, and folded,
     * once for every way down to it.
     */
    private static final class Question {

        private final Map<Core, Boolean> answered = new IdentityHashMap<>();
        private final FoldedValue.Kept folds = new FoldedValue.Kept();
    }

    private WorkedOutToReachIt(InputReading read, Predicate<Denotation> beyond,
                               boolean closuresApart) {
        this(read, beyond, closuresApart, Set.of());
    }

    private WorkedOutToReachIt(InputReading read, Predicate<Denotation> beyond,
                               boolean closuresApart, Set<Core> toldElsewhere) {
        this.read = Objects.requireNonNull(read);
        this.beyond = Objects.requireNonNull(beyond);
        this.closuresApart = closuresApart;
        this.toldElsewhere = toldElsewhere;
    }

    /**
     * The same, for the rest of a comparison a rule read as comparisons of {@code operands}:
     * reading those tells what working each out does, and the rule's statement holds
     * {@code operation}, the one operation on the side the operands are of, to where it answers;
     * none where it is null. What else the comparison works out is asked here as any value is:
     * the other side, the other arguments of the operation, and whatever the operation is
     * written in.
     */
    WorkedOutToReachIt besideWhatWasRestated(List<Core> operands, Core operation) {
        Set<Core> told = Collections.newSetFromMap(new IdentityHashMap<>());
        operands.forEach(each -> told.add(Core.withoutStanding(each)));
        Core answered = operation == null ? null : Core.withoutStanding(operation);
        Predicate<Denotation> before = beyond;
        return new WorkedOutToReachIt(read,
                value -> before.test(value) || Core.withoutStanding(value.value()) == answered,
                closuresApart, told);
    }

    /**
     * What a run works out to reach a value, each node asked of {@link WhatARunMayEndFor} apart
     * from the closures written at it ({@link WhatARunMayEndFor#itselfApartFromTheClosuresWrittenAtIt}),
     * and the body of each such closure worked out with the call.
     */
    static WorkedOutToReachIt of(InputReading read) {
        return new WorkedOutToReachIt(read, _ -> false, true);
    }

    /** The same, each node asked with whatever it applies, and where this says it may end a run,
     *  of {@code beyond}, which knows more of some nodes. */
    static WorkedOutToReachIt asking(InputReading read, Predicate<Denotation> beyond) {
        return new WorkedOutToReachIt(read, beyond, false);
    }

    /**
     * Whether {@code value} itself, apart from what it is made of and what a name in it was given,
     * ends no run: what {@link WhatARunMayEndFor} says of the node, but for a construction, which
     * it leaves unknown because the invariant that may refuse it is the declaration's
     * ({@link #aConstructionEndsNoRun}).
     */
    private boolean itselfEndsNoRun(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        if (written instanceof Core.Construct made) {
            return aConstructionEndsNoRun(made, value.at());
        }
        return (closuresApart ? WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(written)
                : WhatARunMayEndFor.itself(written)).endsNone();
    }

    /**
     * Whether making {@code made} where it stands at {@code at} is refused by no clause: the
     * declaration holds no invariant and spreads none, or every clause of it is read
     * ({@link ClausesInOrder}), working it out ends no run, and it folds to true with its fields
     * standing for what {@code made} hands them. What cannot be shown is not held.
     */
    private boolean aConstructionEndsNoRun(Core.Construct made, InputReads at) {
        if (read.rules().declarations().published().of(made.typeName().key())
                instanceof PublishedDeclarationResult.Found(DeclarationMeaning.Product product)
                && product.clauses().isEmpty() && product.includes().isEmpty()) {
            return true;
        }
        ClausesInOrder clauses = ClausesInOrder.at(made, read.rules());
        if (!clauses.everyRuleReached()) {
            return false;
        }
        for (ClausesInOrder.OneClause clause : clauses.inOrder()) {
            if (!(clause instanceof ClausesInOrder.OneClause.Stated stated)
                    || !WhatARunMayEndFor.of(stated.term()).endsNone()
                    || !Boolean.TRUE.equals(at.forADeclaredRule()
                            .handingTheFields(stated.given(), at, read.rules().newtypes())
                            .folded(stated.term(), read.rules().symbols(),
                                    read.rules().newtypes()).orElse(null))) {
                return false;
            }
        }
        return true;
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
        Predicate<Denotation> before = beyond;
        return new WorkedOutToReachIt(read, value -> before.test(value)
                || (standsFor.contains(Core.withoutStanding(value.value()))
                        && endsOnlyWhereItsOwnAnswerHasNoPlace(
                                Core.withoutStanding(value.value()))),
                closuresApart, toldElsewhere);
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
        return endsNoRun(value, new Question());
    }

    private boolean endsNoRun(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        Boolean known = question.answered.get(written);
        if (known != null) {
            return known;
        }
        boolean endsNone = worksOutWithoutEndingARun(value, question);
        question.answered.put(written, endsNone);
        return endsNone;
    }

    private boolean worksOutWithoutEndingARun(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        if (toldElsewhere.contains(written)) {
            return true;
        }
        if (closuresApart && written instanceof Core.Block closure) {
            return endsNoRun(new Denotation(closure.body(), value.at()), question);
        }
        if (written instanceof Core.LetIn let) {
            return endsNoRun(new Denotation(let.value(), value.at()), question)
                    && endsNoRun(new Denotation(let.body(),
                            value.at().and(let.binder(), let.value())), question);
        }
        // Written in a value that was built, whatever is inside it: the build ran all of it.
        if (written instanceof Core.Construct made && read.rules().declarations().answers()
                .builtWhereItsModuleIsBuilt(read.rules().symbols().module(), made.pos())) {
            return true;
        }
        // A reference to a value is run as the value is defined, which no part of this node says.
        if (written instanceof Core.MaterialisedValue) {
            Denotation defined = value.at().taken(written);
            return defined != null && endsNoRun(defined, question);
        }
        return (itselfEndsNoRun(value) || beyond.test(value)
                || anOperatorWithAValue(value, question))
                && partsAndNamesEndNoRun(value, question);
    }

    /**
     * Whether {@code value} is an operator over numbers the same on every run that has a number:
     * the fold works it out with the run time's own arithmetic, and folds one that aborts to
     * nothing ({@link FoldedValue}). That says what the operator itself comes to and nothing of
     * what is worked out to get its operands, which a fold follows to their values and does not
     * run: the operands are asked as any part is.
     */
    private boolean anOperatorWithAValue(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        return closuresApart && (written instanceof Core.Binary || written instanceof Core.Neg)
                && value.at().folded(written, read.rules().symbols(), read.rules().newtypes(),
                        question.folds).isPresent();
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
        return endsOnlyWhereItsAnswerHasNoPlace(value, new Question());
    }

    private boolean endsOnlyWhereItsAnswerHasNoPlace(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        if (written instanceof Core.LetIn let) {
            return endsNoRun(new Denotation(let.value(), value.at()), question)
                    && endsOnlyWhereItsAnswerHasNoPlace(new Denotation(let.body(),
                            value.at().and(let.binder(), let.value())), question);
        }
        return endsOnlyWhereItsOwnAnswerHasNoPlace(written)
                && partsAndNamesEndNoRun(value, question);
    }

    private boolean partsAndNamesEndNoRun(Denotation value, Question question) {
        for (Core part : whatIsRunWith(Core.withoutStanding(value.value()))) {
            if (!endsNoRun(new Denotation(part, value.at()), question)) {
                return false;
            }
        }
        for (Denotation bound : boundTo(value)) {
            if (!endsNoRun(bound, question)) {
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
