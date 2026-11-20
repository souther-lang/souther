package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BehaviorAnswers;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.CallArguments;
import souther.compiler.check.CalledBody;
import souther.compiler.check.Choice;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.Comparison;
import souther.compiler.check.DeclarationMeaning;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.FoldedValue;
import souther.compiler.check.PublishedDeclarationResult;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.Symbols;
import souther.compiler.check.WalkElements;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.RepresentationBounds;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.ValuesAt;
import souther.compiler.inputs.ValuesHeld;
import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;
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
    /** Expressions whose working out another reading told, whole: one that may end a run here
     *  gets past it all the same. */
    private final Predicate<Denotation> toldElsewhere;
    /** Expressions whose own stop, apart from what they are made of, the analysis that read the
     *  comparison says on each way it reads them in, told or said to be untold: a stop a run may
     *  still come to, said elsewhere, so it answers only whether a stop is left unsaid here
     *  ({@link #leavesItsOwnStopUntold}). */
    private final Predicate<Denotation> ownStopsSaidOnTheirWays;
    /** The arms every run working out what this is asked of has entered, past which it is
     *  asked. */
    private final ArmsTaken onTheWay;

    /**
     * One question asked of what a run works out, for as long as it is asked: what each
     * expression met was answered, and what each name a fold met came to.
     *
     * <p>Within one question an expression is worked out where it is written, a name standing for
     * the one value its binding gave it, so an expression reached from every read of a name is
     * answered once. A chain of names each read more than once is otherwise walked, and folded,
     * once for every way down to it.
     *
     * <p>Asked {@code byTheNumbers} of what a reading passed over, it also answers from the
     * numbers what is worked out comes to: an operation, a total or a closure applied to each
     * element that lies within an {@code Int}. Other readers are not asked so: each of them reads
     * the operations of what may end a run where this sends it, and a value that ends no run by
     * its numbers alone would send it elsewhere.
     */
    private static final class Question {

        /** What each expression was answered, wherever it was read: the node written, and where it
         *  was read told apart by what each name in it stands for, which is what the answer turns
         *  on once the numbers are asked, and by the arms the runs it is asked of entered. Kept
         *  with the questions this one asks past an arm, which differ from it in those arms
         *  alone. */
        private final Map<Core, List<Answered>> answered;
        private final FoldedValue.Kept folds;
        private final boolean byTheNumbers;
        /** The bodies of the closures shown to end no run where the call being asked applies them
         *  ({@link #closuresHeldOverTheirElements}): of that call and no other, so they are held
         *  only by a question asked of its parts, and what that question answers is not kept. */
        private final Set<Core> heldWhereApplied;
        /** What the asker tells the stops of, where this question finds an expression that may
         *  end a run: a stop it tells is no stop this question is about. Asked only of what a run
         *  works out whenever it works out what the question was asked of: none past an arm, nor
         *  in the body of a closure, which works out only what it is handed. */
        private final Predicate<Denotation> tellsWhereItStops;
        /** Where this question asks only whether a stop is left untold, the expressions whose own
         *  stop the analysis says on each way it reads them in
         *  ({@link #besideTheStopsSaidOnTheirWays}); null where it asks whether a run ends, which
         *  a stop said elsewhere does not answer. Asked, as {@link #tellsWhereItStops} is, only of
         *  what a run works out whenever it works out what the question was asked of. */
        private final Predicate<Denotation> ownStopsSaid;
        /** The arms every run working out what this question is asked of has entered. */
        private final ArmsTaken arms;
        /** The arms the runs that work out each value a {@code let} names had entered where they
         *  bound it, by the value written; shared by every question asked from the one that
         *  began the walk. */
        private final Map<Core, List<ArmsTaken>> bound;

        Question(ArmsTaken arms) {
            this(false, arms);
        }

        Question(boolean byTheNumbers, ArmsTaken arms) {
            this(byTheNumbers, null, null, arms);
        }

        Question(boolean byTheNumbers, Predicate<Denotation> tellsWhereItStops,
                 Predicate<Denotation> ownStopsSaid, ArmsTaken arms) {
            this(byTheNumbers, Set.of(), tellsWhereItStops, ownStopsSaid, arms,
                    new IdentityHashMap<>(), new FoldedValue.Kept(), new IdentityHashMap<>());
        }

        private Question(boolean byTheNumbers, Set<Core> heldWhereApplied,
                         Predicate<Denotation> tellsWhereItStops,
                         Predicate<Denotation> ownStopsSaid, ArmsTaken arms,
                         Map<Core, List<Answered>> answered, FoldedValue.Kept folds,
                         Map<Core, List<ArmsTaken>> bound) {
            this.byTheNumbers = byTheNumbers;
            this.heldWhereApplied = heldWhereApplied;
            this.tellsWhereItStops = tellsWhereItStops;
            this.ownStopsSaid = ownStopsSaid;
            this.arms = arms;
            this.answered = answered;
            this.folds = folds;
            this.bound = bound;
        }

        /** A question of the parts of a call that applies the closures {@code held} is shown of,
         *  beside those this one holds. */
        Question applying(Set<Core> held) {
            Set<Core> both = Collections.newSetFromMap(new IdentityHashMap<>());
            both.addAll(heldWhereApplied);
            both.addAll(held);
            return new Question(byTheNumbers, both, tellsWhereItStops, ownStopsSaid, arms,
                    new IdentityHashMap<>(), new FoldedValue.Kept(), bound);
        }

        /** The same question of what only some runs work out, an arm or the body of a closure:
         *  nothing past it is told by the asker or the analysis, since a stop told there would be
         *  one on runs, or of values, that never work it out. */
        Question notOnEveryRun() {
            return (tellsWhereItStops == null && ownStopsSaid == null) ? this
                    : new Question(byTheNumbers, heldWhereApplied, null, null, arms,
                            new IdentityHashMap<>(), new FoldedValue.Kept(), bound);
        }

        /** The same question of arm {@code part} of {@code fork}, read where it is ({@code at}):
         *  of what only the runs entering it work out, which have entered every arm this one
         *  had. */
        Question enteringArm(Core fork, int part, InputReads at) {
            Question past = notOnEveryRun();
            return new Question(byTheNumbers, heldWhereApplied, null, null,
                    arms.entering(fork, part, at), past.answered, past.folds, bound);
        }

        /**
         * The same question of {@code given}, the value a name was given, where it was bound: on
         * the arms the runs binding it had entered there ({@link #binding}), which are some of
         * those this one is asked past, and on none where it was bound outside this walk. A run
         * works the value out before any arm entered between the binding and the name, and on
         * every run that reached the binding, whichever of those arms it enters after.
         *
         * <p>Found by the value written, and not by where it is read: a name's value is read
         * where the name is ({@link InputReads#boundValue}), which is past the binding. Of the
         * arms the value was bound under, those this question was asked past are the walk that
         * reached this name, and the fewest of them are taken: a body is not entered again inside
         * itself, so the walk that reached the name passed the binding under the fewest.
         */
        Question whereItWasBound(Denotation given) {
            ArmsTaken there = null;
            for (ArmsTaken each : bound.getOrDefault(Core.withoutStanding(given.value()),
                    List.of())) {
                if (arms.isPastOrIs(each) && (there == null || there.isPastOrIs(each))) {
                    there = each;
                }
            }
            if (there == null) {
                there = ArmsTaken.NONE;
            }
            return there == arms ? this
                    : new Question(byTheNumbers, heldWhereApplied, tellsWhereItStops,
                            ownStopsSaid, there, answered, folds, bound);
        }

        /** That the value {@code given} a {@code let} names is worked out by runs that entered
         *  the arms this question is asked past. */
        void binding(Core given) {
            List<ArmsTaken> under = bound.computeIfAbsent(Core.withoutStanding(given),
                    _ -> new ArrayList<>());
            for (ArmsTaken each : under) {
                if (each == arms) {
                    return;
                }
            }
            under.add(arms);
        }

        /** Whether the asker tells the stops of {@code value}. */
        boolean tells(Denotation value) {
            return tellsWhereItStops != null && tellsWhereItStops.test(value);
        }

        /** Whether the analysis says the stop of {@code value}'s own working on its ways, where
         *  this asks only whether a stop is left untold. */
        boolean saidItsOwnStop(Denotation value) {
            return ownStopsSaid != null && ownStopsSaid.test(value);
        }

        Boolean answerOf(Core written, InputReads at) {
            for (Answered each : answered.getOrDefault(written, List.of())) {
                if (each.at().equals(at) && each.arms().equals(arms)) {
                    return each.endsNone();
                }
            }
            return null;
        }

        void answer(Core written, InputReads at, boolean endsNone) {
            List<Answered> where = answered.computeIfAbsent(written, _ -> new ArrayList<>());
            where.removeIf(each -> each.at().equals(at) && each.arms().equals(arms));
            where.add(new Answered(at, arms, endsNone));
        }
    }

    /** What {@link #endsNoRun} answered of an expression read where it is ({@code at}), on the
     *  runs that entered {@code arms}. */
    private record Answered(InputReads at, ArmsTaken arms, boolean endsNone) {}

    /** One arm a run entered: arm {@code part} of {@code fork}, as {@link Choice} numbers them,
     *  read where it is ({@code at}). The fork is the node written, told apart from another
     *  written alike. */
    private record ArmTaken(Core fork, int part, InputReads at) {

        @Override
        public boolean equals(Object other) {
            return other instanceof ArmTaken that && fork == that.fork && part == that.part
                    && at.equals(that.at);
        }

        @Override
        public int hashCode() {
            return (System.identityHashCode(fork) * 31 + part) * 31 + at.hashCode();
        }
    }

    /**
     * The arms every run working out an expression has entered on the way to it, outermost first,
     * and the region of the input they leave.
     *
     * <p>What a run entering an arm states ({@link WhatConditionsState#arm}) holds on every run
     * that works out what the arm is made of, so the numbers such a run holds lie where the region
     * narrowed by it leaves them. What a region cannot carry of it narrows nothing, which leaves
     * the region holding every run that enters the arm.
     *
     * <p>An arm stating something no region of the input carries — of a place the reading names
     * no value at — is kept, so that what is answered past it is told apart from what is answered
     * beside it, and narrows nothing ({@link DemandReading#placedInTheRegion}).
     *
     * <p>Told apart by the arms, so that what one way shows is never the answer on another. The
     * region is made only where a reader asks for it, once for the reading whichever reader asks
     * ({@link RegionLeft}), from the region the arms before the last leave.
     */
    private static final class ArmsTaken {

        static final ArmsTaken NONE = new ArmsTaken(List.of(), null);

        private final List<ArmTaken> arms;
        /** These without the last arm, or null where there are none. */
        private final ArmsTaken past;
        private RegionLeft left;
        /** The reading {@code left} was asked under. */
        private InputReading leftOf;

        private ArmsTaken(List<ArmTaken> arms, ArmsTaken past) {
            this.arms = arms;
            this.past = past;
        }

        boolean isEmpty() {
            return arms.isEmpty();
        }

        /** These, and arm {@code part} of {@code fork} read at {@code at} past them. */
        ArmsTaken entering(Core fork, int part, InputReads at) {
            List<ArmTaken> more = new ArrayList<>(arms);
            more.add(new ArmTaken(fork, part, at));
            return new ArmsTaken(List.copyOf(more), this);
        }

        /** Whether these are {@code earlier}, or were entered past it: the very arms taken on
         *  the way here, and not others equal to them. */
        boolean isPastOrIs(ArmsTaken earlier) {
            for (ArmsTaken each = this; each != null; each = each.past) {
                if (each == earlier) {
                    return true;
                }
            }
            return false;
        }

        /** The region of the input every run that entered these leaves, under {@code read}: what
         *  the declarations leave where there are none. */
        SearchRegion region(InputReading read) {
            return left(read).region();
        }

        /** Whether the region these leave is shown to hold no row, under {@code read}: no run
         *  enters every one of them, and nothing past them is worked out on any run. */
        boolean leaveNoRun(InputReading read) {
            return !arms.isEmpty() && left(read).holdsNoRow();
        }

        /** What these leave under {@code read}: the one the reading keeps for no arm, or what the
         *  one before keeps for the last arm. Kept with these, but for no arm, which stands for
         *  every reading. */
        private RegionLeft left(InputReading read) {
            if (arms.isEmpty()) {
                return read.derived(RegionLeft.class,
                        _ -> new RegionLeft(read.quantities().region()));
            }
            if (left == null || leftOf != read) {
                leftOf = read;
                left = past.left(read).past(arms.getLast(), read);
            }
            return left;
        }

        @Override
        public boolean equals(Object other) {
            return this == other || (other instanceof ArmsTaken that && arms.equals(that.arms));
        }

        @Override
        public int hashCode() {
            return arms.hashCode();
        }
    }

    /**
     * The region a run that entered some arms leaves, whether it is shown to hold no row, which is
     * asked of it only where a reader asks and then once, and what a run entering one more arm
     * leaves, by that arm.
     *
     * <p>Kept with the reading of the input from the region it leaves with no arm entered: a
     * function of the arms and the reading alone, asked by every reader of what a run works out
     * over the same body. One arm past another is asked of the one before by that arm alone, so
     * what a list of arms leaves is found one arm at a time and never by the whole list.
     */
    private static final class RegionLeft {

        private final SearchRegion region;
        private volatile Boolean holdsNoRow;
        private final Map<ArmTaken, RegionLeft> past = new ConcurrentHashMap<>();

        RegionLeft(SearchRegion region) {
            this.region = region;
        }

        SearchRegion region() {
            return region;
        }

        /** What a run that also entered {@code arm} leaves: this region narrowed by what entering
         *  it states, as far as the region carries it, and where the region can be asked it. */
        RegionLeft past(ArmTaken arm, InputReading read) {
            RegionLeft known = past.get(arm);
            if (known != null) {
                return known;
            }
            SearchRegion narrowed = region;
            Proposition stated = WhatConditionsState.of(read)
                    .arm(arm.fork(), arm.part(), arm.at()).proposition();
            if (DemandReading.placedInTheRegion(stated, read)) {
                for (TakenConstraint taken : DemandReading.regionAnswered(stated, read)
                        .narrowing()) {
                    narrowed = taken.narrowing(narrowed);
                }
            }
            RegionLeft made = new RegionLeft(narrowed);
            RegionLeft had = past.putIfAbsent(arm, made);
            return had != null ? had : made;
        }

        boolean holdsNoRow() {
            Boolean known = holdsNoRow;
            if (known == null) {
                known = region.emptiness().isPresent();
                holdsNoRow = known;
            }
            return known;
        }
    }

    private WorkedOutToReachIt(InputReading read, Predicate<Denotation> beyond,
                               boolean closuresApart) {
        this(read, beyond, closuresApart, _ -> false, _ -> false, ArmsTaken.NONE,
                new IdentityHashMap<>());
    }

    private WorkedOutToReachIt(InputReading read, Predicate<Denotation> beyond,
                               boolean closuresApart, Predicate<Denotation> toldElsewhere,
                               Predicate<Denotation> ownStopsSaidOnTheirWays,
                               ArmsTaken onTheWay, Map<Core, List<NumbersAt>> numbersAsked) {
        this.read = Objects.requireNonNull(read);
        this.beyond = Objects.requireNonNull(beyond);
        this.closuresApart = closuresApart;
        this.toldElsewhere = toldElsewhere;
        this.ownStopsSaidOnTheirWays = Objects.requireNonNull(ownStopsSaidOnTheirWays);
        this.onTheWay = onTheWay;
        this.numbersAsked = numbersAsked;
    }

    /**
     * The same, where the analysis that read the comparison says, on each way it reads them in,
     * the own stop of every expression {@code said} holds of: a total read once for every way of
     * keeping its elements, each way's total told as the operation it is or said to be left
     * untold. What such an expression is made of is asked here as before, and a run may still
     * stop in it, so it is no stop left unsaid here and nothing a row is shown to get past.
     */
    WorkedOutToReachIt besideTheStopsSaidOnTheirWays(Predicate<Core> said) {
        Predicate<Denotation> before = ownStopsSaidOnTheirWays;
        return new WorkedOutToReachIt(read, beyond, closuresApart, toldElsewhere,
                value -> before.test(value) || said.test(value.value()), onTheWay,
                numbersAsked);
    }

    /**
     * Whether working out {@code value}, which a reading passed over, leaves a stop of its own
     * unsaid: it may end a run, apart from what it is made of and what a name in it was given
     * ({@link #ownWorkingEndsNoRun}), and the analysis does not say it on each way.
     */
    boolean leavesItsOwnStopUntold(Denotation value) {
        return !ownWorkingEndsNoRun(value) && !ownStopsSaidOnTheirWays.test(value);
    }

    /**
     * The same, of what only the runs entering arm {@code part} of {@code fork}, read where it is
     * ({@code at}), work out: what entering it states narrows the numbers they hold
     * ({@link ArmsTaken}).
     */
    WorkedOutToReachIt onTheArm(Core fork, int part, InputReads at) {
        return new WorkedOutToReachIt(read, beyond, closuresApart, toldElsewhere,
                ownStopsSaidOnTheirWays, onTheWay.entering(Core.withoutStanding(fork), part, at),
                numbersAsked);
    }

    /** The same, of {@code part} of {@code written} read at {@code at}: on its arm where it is
     *  one ({@link #onTheArm}), and as this where it is not. */
    WorkedOutToReachIt onThe(Core written, Part part, InputReads at) {
        return part.arm() < 0 ? this : onTheArm(written, part.arm(), at);
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
                closuresApart, value -> told.contains(Core.withoutStanding(value.value())),
                ownStopsSaidOnTheirWays, onTheWay, numbersAsked);
    }

    /**
     * The same, with every expression {@code told} says another reading told the working out of,
     * whole, wherever it is met: what such an expression is made of is not asked here.
     */
    WorkedOutToReachIt besideWhatIsTold(Predicate<Denotation> told) {
        Predicate<Denotation> before = toldElsewhere;
        return new WorkedOutToReachIt(read, beyond, closuresApart,
                value -> before.test(value) || told.test(value), ownStopsSaidOnTheirWays,
                onTheWay, numbersAsked);
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
     * it leaves unknown because the invariant that may refuse it is the declaration's. A
     * construction ends none where an attempt makes it ({@link InputReads#builtByAnAttempt}),
     * where the discharge check proved every clause of it under what holds where it is made
     * ({@link BehaviorAnswers#shownToHold}), and where its clauses fold to true over what it is
     * handed ({@link #aConstructionEndsNoRun}).
     */
    private boolean itselfEndsNoRun(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        if (written instanceof Core.Construct made) {
            return value.at().builtByAnAttempt(made)
                    || read.rules().declarations().answers()
                            .shownToHold(read.rules().symbols().module(), made)
                    || aConstructionEndsNoRun(made, value.at());
        }
        if (stopsOnlyOnAnOperandThatIsNotNought(value)) {
            return true;
        }
        if (!closuresApart) {
            return WhatARunMayEndFor.itself(written).endsNone()
                    || endsARowsRunOnlyPastTheRepresentation(written);
        }
        // The sites a library call works out are the ones it may end a run at, and it ends none
        // where the library shows it answers whatever it is handed.
        return WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(written).endsNone()
                || completionOfARowsRun(written) instanceof GetsPast.Always;
    }

    /**
     * Whether {@code value} is an operation that ends a run on its divisor alone, only where that
     * is nought, as the operation's owner says ({@link Pullback#theDivisorItAloneStopsOn}), and
     * the divisor comes to another whole number whatever the run is: {@code Int.floorMod(x, 7)}
     * ends none.
     */
    private boolean stopsOnlyOnAnOperandThatIsNotNought(Denotation value) {
        Core operand = Pullback.theDivisorItAloneStopsOn(value.value());
        return operand != null && value.at().folded(operand, read.rules().symbols(),
                read.rules().newtypes()).orElse(null) instanceof Long by && by != 0;
    }

    /**
     * Where {@code e} itself answers on a run of a row, apart from the closures written at it: as
     * its owner says ({@link WhatARunMayEndFor#completionApartFromTheClosuresWrittenAtIt}), but
     * everywhere where it ends a run only past what the representation holds
     * ({@link GetsPast#endsOnlyPastTheRepresentation}).
     *
     * <p>A class is drawn over the values a model tells apart, and where a {@code String} or a
     * collection stops is none of those: the longest string ends no class of a length
     * ({@link ResultBound.Limit}), and a run stopped only because an answer is past it does not
     * part the values either. So the runs a relation is read over are taken to get past such an
     * operation, and that a run stops there is said once, of the operation
     * ({@link StopPastTheRepresentation}). What the owner says stands for every reader that is
     * not drawing classes: a proof that a body ends no run asks the owner.
     */
    static GetsPast completionOfARowsRun(Core e) {
        GetsPast owned = WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(e);
        return owned.endsOnlyPastTheRepresentation() ? new GetsPast.Always() : owned;
    }

    /**
     * Whether {@code e}, read whole, ends a run only past what the representation holds: where
     * what it ends a run for whole is what it ends one for apart from the closures written at it,
     * as the owner says both, where it answers apart from them is where it answers.
     */
    private static boolean endsARowsRunOnlyPastTheRepresentation(Core e) {
        return WhatARunMayEndFor.itself(e)
                .equals(WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(e))
                && WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(e)
                        .endsOnlyPastTheRepresentation();
    }

    /**
     * Whether making {@code made} where it stands at {@code at} is refused by no clause: the
     * declaration holds no invariant and spreads none, or every clause of it is read
     * ({@link ClausesInOrder}), working it out ends no run, and it folds to true with its fields
     * standing for what {@code made} hands them. What cannot be shown is not held.
     */
    boolean aConstructionEndsNoRun(Core.Construct made, InputReads at) {
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
                    || !Boolean.TRUE.equals(at.forADeclaredRule(stated.elements())
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
                closuresApart, toldElsewhere, ownStopsSaidOnTheirWays, onTheWay, numbersAsked);
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
        return endsNoRun(value, new Question(onTheWay));
    }

    /** Whether working out {@code closure} where {@code call} applies it ends no run: asked with
     *  what the call hands it ({@link #closuresHeldOverTheirElements}). */
    boolean endsNoRunWhereApplied(Denotation call, Core.Block closure) {
        Question question = new Question(true, onTheWay);
        return endsNoRun(new Denotation(closure, call.at()),
                question.applying(closuresHeldOverTheirElements(call, question)));
    }

    private boolean endsNoRun(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        if (question.heldWhereApplied.contains(written)) {
            return true;
        }
        Boolean known = question.answerOf(written, value.at());
        if (known != null) {
            return known;
        }
        boolean endsNone = worksOutWithoutEndingARun(value, question);
        question.answer(written, value.at(), endsNone);
        return endsNone;
    }

    /** Asked of what {@code value} is made of first, so that what another reading tells is only
     *  ever the least of it that may end a run: telling a value names what it reads. */
    private boolean worksOutWithoutEndingARun(Denotation value, Question question) {
        return worksOutOfItselfWithoutEndingARun(value, question) || toldElsewhere.test(value)
                || question.tells(value);
    }

    private boolean worksOutOfItselfWithoutEndingARun(Denotation value, Question question) {
        // Past arms no run enters together, nothing is worked out on any run.
        if (question.arms.leaveNoRun(read)) {
            return true;
        }
        Core written = Core.withoutStanding(value.value());
        if (closuresApart && written instanceof Core.Block closure) {
            return endsNoRun(new Denotation(closure.body(), value.at()),
                    question.notOnEveryRun());
        }
        if (written instanceof Core.LetIn let) {
            question.binding(let.value());
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
            return defined != null && endsNoRun(defined, question.whereItWasBound(defined));
        }
        if (question.byTheNumbers) {
            Set<Core> held = closuresHeldOverTheirElements(value, question);
            if (!held.isEmpty()) {
                Question applying = question.applying(held);
                return ownWorkingEndsNoRun(value, applying)
                        && partsAndNamesEndNoRun(value, applying);
            }
        }
        return ownWorkingEndsNoRun(value, question) && partsAndNamesEndNoRun(value, question);
    }

    /** The ends of an {@code Int}, which a total of whole numbers and each operation of them
     *  answers within. */
    private static final WhereAnOperatorAnswers.WhereItsExactValueIsHeld AN_INT =
            (WhereAnOperatorAnswers.WhereItsExactValueIsHeld) WhereAnOperatorAnswers.ofATotal(
                    Type.INT);

    /**
     * What a closure {@code walk} applies works out of each element it is handed
     * ({@link AddedOfEachElement#ofAnAnswer}), with what each path of the element comes to and how
     * many elements there are at most; null where {@code walk} applies none, or it is not read so.
     *
     * @param rangeOf what a path of the element comes to: the numbers its place holds, the code
     *                points of a string from nought to the last there is, the position from
     *                nought to one below the most elements; null where none of these
     * @param most    the elements of the list written out at the call, or the most a list holds;
     *                null where neither is known
     */
    private record Worth(AddedOfEachElement added, Function<Core, FormRange> rangeOf, Core body,
                         Long most) {}

    private Worth whatEachElementIsWorth(Denotation walk, Question question) {
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        Denotation met = walk.at().denotes(walk.value(), symbols, newtypes);
        InputReads where = met == null ? null : met.at();
        BindingId element = where == null ? null
                : WalkElements.elementBindingOf(met.value(), where, symbols, newtypes);
        ElementAnswer answer = element == null ? null : where.answerAt(element);
        Core container = answer == null ? null : where.containerOfTheElementHandedTo(element);
        AddedOfEachElement added = container == null ? null : AddedOfEachElement.ofAnAnswer(
                answer, decides -> endsNoRun(new Denotation(decides, where), question), newtypes);
        if (added == null) {
            return null;
        }
        Long most = mostElementsOf(container);
        return new Worth(added, rangesOfTheElements(where, element, answer.position(), container,
                added.aliases(), most), answer.body(), most);
    }

    /** How many elements {@code container} holds at most: those of a list written out there, or
     *  the most a list holds; null where neither is known. */
    private static Long mostElementsOf(Core container) {
        return Core.withoutStanding(container) instanceof Core.ListLit list
                ? Long.valueOf(list.elements().size()) : RepresentationBounds.mostElements();
    }

    /**
     * What a path of the element handed on {@code element} comes to, read in {@code where}: the
     * numbers its place holds, wherever the elements of {@code container} stand; the code point
     * of a string, from nought to the last there is; or, where it is the position handed on
     * {@code position}, from nought to one below {@code most}. Null where it is none of these.
     */
    private Function<Core, FormRange> rangesOfTheElements(
            InputReads where, BindingId element, BindingId position, Core container,
            Map<BindingId, Core> aliases, Long most) {
        DeclarationNewtypes newtypes = read.rules().newtypes();
        NumericTerm aCodePoint = InputNumber.aCodePointListedBy(container, read.domain(), where,
                read.rules());
        ValuesHeld held = where.everyElementAt(element, newtypes);
        Function<ElementProjection, FormRange> kept = keptByATest(where, element, container);
        return path -> {
            if (position != null && Core.withoutStanding(path) instanceof Core.Read at
                    && position.equals(at.binding())) {
                return (most == null || most < 1) ? null
                        : new FormRange(ExactRatio.ZERO, ExactRatio.of(most - 1));
            }
            ElementProjection place = ElementProjection.read(path, element, aliases, newtypes);
            if (place == null) {
                return null;
            }
            return switch (held) {
                case ValuesHeld.At(TermPath at) -> rangeOfAPlace(place.from(at), ArmsTaken.NONE);
                case ValuesHeld.MayStandAt(List<TermPath> among) -> {
                    FormRange hull = null;
                    for (TermPath each : among) {
                        FormRange one = rangeOfAPlace(place.from(each), ArmsTaken.NONE);
                        if (one == null) {
                            yield null;
                        }
                        hull = hull == null ? one : hull.hull(one);
                    }
                    yield hull;
                }
                case ValuesHeld.NotAPosition _ -> place.steps().isEmpty() && aCodePoint != null
                        ? FormRange.endsOf(aCodePoint, read)
                        : kept == null ? null : kept.apply(place);
            };
        };
    }

    /**
     * What a path of the element handed on {@code element} comes to where {@code container} keeps
     * the elements of another container a test holds of
     * ({@link BoundOperationFacts#keepsWhereItHolds}), as the library says it does:
     * an element kept is one of that container's, standing where its elements stand
     * ({@link InputReads#elementAt}), and one the test held of ({@link #heldByTheTest}). Null where
     * the container keeps by no test, the test is no closure of one value, or its elements stand at
     * no place.
     */
    private Function<ElementProjection, FormRange> keptByATest(InputReads where, BindingId element,
                                                               Core container) {
        DeclarationNewtypes newtypes = read.rules().newtypes();
        if (!(Core.withoutStanding(container) instanceof Core.PreservedCall call)) {
            return null;
        }
        BoundOperationFacts.Kept keeps =
                DefaultBoundOperationFacts.get().keepsWhereItHolds(call.operation());
        if (keeps == null
                || !(Core.withoutStanding(CallArguments.of(keeps.closure(), call))
                        instanceof Core.Block test)
                || test.params().size() != 1
                || !(where.elementAt(element, newtypes) instanceof ValuesAt.At(TermPath at))) {
            return null;
        }
        BindingId tested = test.params().getFirst().binding();
        return place -> heldByTheTest(rangeOfAPlace(place.from(at), ArmsTaken.NONE), place,
                test.body(), tested, where);
    }

    /**
     * {@code range}, the numbers the path {@code place} of a value comes to, held to what
     * {@code test} holding of that value, handed on {@code tested}, says of the path: each
     * comparison of the path with a number written down, and both sides of {@code &&}. As it is
     * where the test says nothing such of it; null where no number of it meets the test.
     */
    private FormRange heldByTheTest(FormRange range, ElementProjection place, Core test,
                                    BindingId tested, InputReads at) {
        if (range == null || !(Core.withoutStanding(test) instanceof Core.Binary binary)) {
            return range;
        }
        // Both sides hold of a value kept where the operator joins them so; a side of any other
        // join holds of some kept values and not of others, and says nothing of every one.
        if (ConditionJoin.of(binary.op()).orElse(null) == ConditionJoin.BOTH) {
            return heldByTheTest(heldByTheTest(range, place, binary.left(), tested, at), place,
                    binary.right(), tested, at);
        }
        if (!(Comparison.of(binary).orElse(null) instanceof Comparison compared)) {
            return range;
        }
        DeclarationNewtypes newtypes = read.rules().newtypes();
        Rel rel = compared.claim().statedRelation();
        if (place.equals(ElementProjection.read(compared.left(), tested, Map.of(), newtypes))
                && at.folded(compared.right(), read.rules().symbols(), newtypes).orElse(null)
                        instanceof Long number) {
            return range.heldTo(rel, ExactRatio.of(number));
        }
        if (place.equals(ElementProjection.read(compared.right(), tested, Map.of(), newtypes))
                && at.folded(compared.left(), read.rules().symbols(), newtypes).orElse(null)
                        instanceof Long number) {
            return range.heldTo(rel.turned(), ExactRatio.of(number));
        }
        return range;
    }

    /** The numbers {@code place} holds on the runs that entered {@code arms}, held to where the
     *  region they leave runs it, or null where it is under nothing this reading holds. */
    private FormRange rangeOfAPlace(TermPath place, ArmsTaken arms) {
        NumericTerm at = new NumericTerm.ValueOf(place);
        if (!read.quantities().answersFor(at)) {
            return null;
        }
        FormRange held = FormRange.held(LinearForm.atom(at), read, Map.of());
        if (held == null || arms.isEmpty()) {
            return held;
        }
        // Where the arms leave no row, no run gets here and nothing is known of it.
        NumericDomain.FormProjection runs = arms.region(read).projectionOf(LinearForm.atom(at));
        if (runs instanceof NumericDomain.FormProjection.NothingIsLeft) {
            return null;
        }
        return runs instanceof NumericDomain.FormProjection.Within within
                ? held.heldTo(within.bounds()) : held;
    }

    /**
     * The body of the closure {@code value} applies to each element, shown to end no run where
     * every operation it works out of an element lies within an {@code Int}, from what the
     * element comes to ({@link #whatEachElementIsWorth}); and a walk's step, where every number
     * the walk works out from its seed over the most elements there are does
     * ({@link AddedOfEachElement#heldOverEveryStep}). Asked where the call is, which knows the
     * elements, and not where the closure's body is met, which knows nothing of them: what it
     * shows is of this call, whose question holds it ({@link Question#applying}), and of no other
     * call the same closure is handed to. None where it shows nothing.
     */
    private Set<Core> closuresHeldOverTheirElements(Denotation value, Question question) {
        if (!closuresApart || !(Core.withoutStanding(value.value()) instanceof Core.PreservedCall)) {
            return Set.of();
        }
        Worth each = whatEachElementIsWorth(value, question);
        if (each != null && each.added().holdsEveryOperation(each.rangeOf(), AN_INT.least(),
                AN_INT.greatest())) {
            return Set.of(Core.withoutStanding(each.body()));
        }
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        Denotation met = value.at().denotes(value.value(), symbols, newtypes);
        SeededWalk walk = met == null ? null : SeededWalk.of(met.value(), closure ->
                Core.withoutStanding(closure) instanceof Core.Block block ? block : null);
        InputReads where = met == null ? null : met.at();
        AddedOfEachElement step = walk == null ? null : AddedOfEachElement.ofTheStep(walk,
                decides -> endsNoRun(new Denotation(decides, where), question), newtypes);
        Long most = step == null ? null : mostElementsOf(walk.container());
        if (most != null && where.folded(walk.seed(), symbols, newtypes).orElse(null)
                instanceof Long seed
                && step.heldOverEveryStep(BigInteger.valueOf(seed), rangesOfTheElements(where,
                        walk.element().binding(), null, walk.container(), step.aliases(), most),
                        most, AN_INT.least(), AN_INT.greatest())) {
            return Set.of(Core.withoutStanding(walk.step().body()));
        }
        return Set.of();
    }

    /**
     * Whether {@code value} is a total of whole numbers, held to an {@code Int} and ending a run
     * only past it ({@link GetsPast.WhereTheTotalFits}), that no list can take past it: each
     * element comes to numbers whose sum over the most elements there are lies within it — what a
     * closure works out of each ({@link #whatEachElementIsWorth}), or the numbers a list written
     * out holds, every one of them there.
     */
    boolean aTotalWithinAnInt(Denotation value) {
        if (!(Core.withoutStanding(value.value()) instanceof Core.PreservedCall call)
                || !(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(call)
                        instanceof GetsPast.WhereTheTotalFits(int list))
                || list >= call.args().size()) {
            return false;
        }
        Denotation listed = new Denotation(call.args().get(list), value.at());
        Worth each = whatEachElementIsWorth(listed, new Question(onTheWay));
        if (each != null) {
            FormRange one = each.added().answerHeldWithin(each.rangeOf(), AN_INT.least(),
                    AN_INT.greatest());
            if (one == null || each.most() == null) {
                return false;
            }
            ExactRatio most = ExactRatio.of(each.most());
            FormRange total = FormRange.combined(BinOp.MUL, one,
                    new FormRange(ExactRatio.ZERO, most));
            return total != null && total.hull(new FormRange(ExactRatio.ZERO, ExactRatio.ZERO))
                    .liesWithin(AN_INT.least(), AN_INT.greatest());
        }
        return aListWrittenOutWithinAnInt(listed);
    }

    /** Whether {@code listed} is a list written out, every element there and a number the fold
     *  works out, whose sum lies within an {@code Int}. */
    private boolean aListWrittenOutWithinAnInt(Denotation listed) {
        if (!(WrittenOutElements.of(listed, read.rules().symbols(), read.rules().newtypes())
                instanceof WrittenOutElements.Walked.Each written)) {
            return false;
        }
        BigInteger sum = BigInteger.ZERO;
        for (ReadMeaning.Occurrence each : written.asWritten()) {
            Denotation element = each.value();
            if (!each.keptWhere().isEmpty()
                    || !(element.at().folded(element.value(), read.rules().symbols(),
                            read.rules().newtypes()).orElse(null) instanceof Long number)) {
                return false;
            }
            sum = sum.add(BigInteger.valueOf(number));
        }
        return sum.compareTo(AN_INT.least()) >= 0 && sum.compareTo(AN_INT.greatest()) <= 0;
    }

    /**
     * Whether working out {@code value}, which a reading passed over, ends no run of its own,
     * apart from what it is made of and what a name in it was given, which are asked as values of
     * their own: asked {@link Question#byTheNumbers}.
     */
    boolean ownWorkingEndsNoRun(Denotation value) {
        return ownWorkingEndsNoRun(value, new Question(true, onTheWay));
    }

    /**
     * The same, asked of {@code question}. Past an arm an operation is asked by its numbers on the
     * runs entering the arm, however the question was asked: nothing the asker reads of the
     * comparison is a stop of those runs alone ({@link Question#enteringArm}), so an operation
     * there is sent to no reader that would tell where it stops.
     */
    private boolean ownWorkingEndsNoRun(Denotation value, Question question) {
        return itselfEndsNoRun(value) || beyond.test(value) || question.saidItsOwnStop(value)
                || anOperatorWithAValue(value, question)
                || (question.byTheNumbers && aTotalWithinAnInt(value))
                || ((question.byTheNumbers || !question.arms.isEmpty())
                        && anOperatorWithinAnInt(value, question.arms));
    }

    /** Whether working out {@code value}, which a reading passed over, ends no run, asked
     *  {@link Question#byTheNumbers}. */
    boolean endsNoRunWhereItWasPassedOver(Denotation value) {
        return endsNoRun(value, new Question(true, onTheWay));
    }

    /**
     * The same, where the asker tells the stops of what it can ({@code tells}): whether every
     * stop a run may come to working {@code value} out is either none or told. Asked of what may
     * end a run least first, so what is told is only ever the least of it; and only of what every
     * run working {@code value} out works out, so nothing an arm or a closure's body holds is told
     * as a stop of runs, or of values, that never work it out
     * ({@link Question#notOnEveryRun}).
     */
    boolean endsNoRunUntoldWhereItWasPassedOver(Denotation value,
                                               Predicate<Denotation> tells) {
        return endsNoRun(value, new Question(true, tells, ownStopsSaidOnTheirWays, onTheWay));
    }

    /**
     * Whether working out {@code value}, which a reading passed over, leaves no stop unsaid: every
     * stop a run may come to there is none, or one the analysis says on each way
     * ({@link #besideTheStopsSaidOnTheirWays}). Not whether a run ends, which a stop said
     * elsewhere does not answer.
     */
    boolean leavesNoStopUntoldWhereItWasPassedOver(Denotation value) {
        return endsNoRun(value, new Question(true, null, ownStopsSaidOnTheirWays, onTheWay));
    }

    /**
     * Whether {@code value} is a sum, a difference, a product or a negation of whole numbers whose
     * operands come to numbers ({@link #numbersOf}), on the runs that entered {@code arms}, it
     * takes to no number past an {@code Int}.
     */
    private boolean anOperatorWithinAnInt(Denotation value, ArmsTaken arms) {
        FormRange range = Core.withoutStanding(value.value()).type() == Type.INT
                ? whatItComesTo(value, arms) : null;
        return range != null && range.liesWithin(AN_INT.least(), AN_INT.greatest());
    }

    /**
     * The numbers {@code value} works out, on the runs that entered {@code arms}, from the numbers
     * its operands come to, before its type holds them: a sum, a difference, a product or a
     * negation, or what a call of the library answers in each case it is defined in
     * ({@link Choice#casesOf}) where all it ends a run for is that answer having no place. Null
     * where it is none of these or that is not known.
     */
    private FormRange whatItComesTo(Denotation value, ArmsTaken arms) {
        Function<Core, FormRange> operand = each -> numbersOf(new Denotation(each, value.at()),
                arms);
        return switch (Core.withoutStanding(value.value())) {
            case Core.Binary binary when binary.op() == BinOp.ADD || binary.op() == BinOp.SUB
                    || binary.op() == BinOp.MUL -> FormRange.combined(binary.op(),
                    operand.apply(binary.left()), operand.apply(binary.right()));
            case Core.Neg negated -> FormRange.combined(BinOp.SUB,
                    new FormRange(ExactRatio.ZERO, ExactRatio.ZERO),
                    operand.apply(negated.operand()));
            case Core.PreservedCall call when endsOnlyWhereItsOwnAnswerHasNoPlace(call) -> {
                FormRange hull = null;
                List<Choice.ADefinitionCase> cases = Choice.casesOf(call);
                for (Choice.ADefinitionCase each : cases) {
                    FormRange one = FormRange.of(each.answers(), operand);
                    if (one == null) {
                        yield null;
                    }
                    hull = hull == null ? one : hull.hull(one);
                }
                yield hull;
            }
            default -> null;
        };
    }

    /**
     * The constructions {@code value} may be, each where it is written, or null where that is not
     * known: a construction itself, what every value a name was given may be, what a behavior's
     * body may be, either arm of a choice, and what a walk from a seed may end with whose step
     * answers the element or what it was carried and nothing else — the seed or an element of the
     * list written out it walks.
     */
    private List<Denotation> valuesItMayBe(Denotation value) {
        Core written = Core.withoutStanding(value.value());
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        return switch (written) {
            case Core.Construct _ -> List.of(value);
            case Core.Read _ -> {
                List<Denotation> given = boundTo(value);
                yield given.isEmpty() ? null : allOf(given.stream().map(this::valuesItMayBe)
                        .toList());
            }
            case Core.If fork -> {
                // An arm whose values are not known is null, and then so is the answer for both.
                List<List<Denotation>> parts = new ArrayList<>();
                parts.add(valuesItMayBe(new Denotation(fork.then(), value.at())));
                parts.add(valuesItMayBe(new Denotation(fork.els(), value.at())));
                yield allOf(parts);
            }
            case Core.Call _ when AnOperationApplied.of(written) instanceof AnOperationApplied
                    applied && applied.operation() instanceof ValueName.Behavior behavior
                    && !value.at().standsIn(behavior) -> {
                Optional<CalledBody> body =
                        read.rules().declarations().answers().bodyOf(behavior);
                InputReads inside = body.isEmpty() ? null : value.at().calling(behavior,
                        body.get(), applied.args(), newtypes);
                yield inside == null ? null
                        : valuesItMayBe(new Denotation(body.get().body(), inside));
            }
            case Core.PreservedCall _ -> {
                Denotation met = value.at().denotes(written, symbols, newtypes);
                SeededWalk walk = met == null ? null : SeededWalk.of(met.value(), closure ->
                        Core.withoutStanding(closure) instanceof Core.Block block ? block : null);
                List<Denotation> elements = walk == null
                        || !answersTheElementOrWhatItCarried(walk.step().body(),
                                walk.element().binding(), walk.accumulator().binding()) ? null
                        : elementsWrittenOut(new Denotation(walk.container(), met.at()));
                if (elements == null) {
                    yield null;
                }
                List<List<Denotation>> parts = new ArrayList<>();
                parts.add(valuesItMayBe(new Denotation(walk.seed(), met.at())));
                for (Denotation one : elements) {
                    parts.add(valuesItMayBe(one));
                }
                yield allOf(parts);
            }
            case Core.LetIn let -> valuesItMayBe(new Denotation(let.body(),
                    value.at().and(let.binder(), let.value())));
            // A run of names read off one value, read one name at a time.
            case Core.FieldProjection projection ->
                    valuesItMayBe(new Denotation(projection.lastAccess(), value.at()));
            case Core.FieldAccess access -> {
                List<Denotation> holding = valuesItMayBe(new Denotation(access.target(),
                        value.at()));
                if (holding == null) {
                    yield null;
                }
                List<List<Denotation>> parts = new ArrayList<>();
                for (Denotation each : holding) {
                    Core field = fieldOf(each, access.field());
                    parts.add(field == null ? null
                            : valuesItMayBe(new Denotation(field, each.at())));
                }
                yield allOf(parts);
            }
            default -> null;
        };
    }

    /** The value {@code made}, a construction, gives {@code field}, or null where it gives it
     *  none. */
    private static Core fieldOf(Denotation made, String field) {
        return ((Core.Construct) Core.withoutStanding(made.value())).values().stream()
                .filter(one -> one.field().equals(field))
                .map(Core.FieldValue::value).findFirst().orElse(null);
    }

    /** Every element of {@code list} where it is a list written out, each as written — through a
     *  value it refers to, run as the value is defined, or the one value a name was given — or
     *  null where it is none. */
    private List<Denotation> elementsWrittenOut(Denotation list) {
        Core written = Core.withoutStanding(list.value());
        if (written instanceof Core.MaterialisedValue) {
            Denotation defined = list.at().taken(written);
            return defined == null ? null : elementsWrittenOut(defined);
        }
        if (written instanceof Core.Read && boundTo(list) instanceof List<Denotation> given
                && given.size() == 1) {
            return elementsWrittenOut(given.getFirst());
        }
        if (written instanceof Core.ListLit literal) {
            return literal.elements().stream().map(each -> new Denotation(each, list.at()))
                    .toList();
        }
        return WrittenOutElements.of(list, read.rules().symbols(), read.rules().newtypes())
                instanceof WrittenOutElements.Walked.Each each
                ? each.asWritten().stream().map(ReadMeaning.Occurrence::value).toList() : null;
    }

    /** Whether {@code body} answers the element handed on {@code element} or what was carried
     *  on {@code carried}, whichever arm of a choice it takes, and nothing else. */
    private static boolean answersTheElementOrWhatItCarried(Core body, BindingId element,
                                                           BindingId carried) {
        return switch (Core.withoutStanding(body)) {
            case Core.Read name -> element.equals(name.binding()) || carried.equals(name.binding());
            case Core.If fork -> answersTheElementOrWhatItCarried(fork.then(), element, carried)
                    && answersTheElementOrWhatItCarried(fork.els(), element, carried);
            default -> false;
        };
    }

    /** Every one of {@code parts} together, or null where one is not known. */
    private static List<Denotation> allOf(List<List<Denotation>> parts) {
        List<Denotation> out = new ArrayList<>();
        for (List<Denotation> each : parts) {
            if (each == null) {
                return null;
            }
            out.addAll(each);
        }
        return out;
    }

    /** The numbers of {@code range} an {@code Int} holds: those a run that got the value holds,
     *  past which it stopped. Null where it is not known or holds none. */
    private static FormRange heldToAnInt(FormRange range) {
        return range == null ? null : range.meet(new FormRange(ExactRatio.of(AN_INT.least()),
                ExactRatio.of(AN_INT.greatest())));
    }

    /**
     * The numbers {@code value} comes to, or null where that is not known: a number the fold works
     * out, what the place of the input it reads holds, what every value a name was given comes to,
     * what the library declares a call answers for the numbers it is handed
     * ({@link ResultRange}), what an operation makes of its operands' numbers, and either arm of a
     * choice, each on the runs that enter it. Each expression is asked once
     * ({@link #numbersAsked}), where it is written, as an expression {@link #endsNoRun} meets is.
     * On the runs that entered the arms this is asked past ({@link #onTheArm}).
     */
    FormRange numbersOf(Denotation value) {
        return numbersOf(value, onTheWay);
    }

    /** What {@link #numbersOf} answered of an expression read where it is ({@code at}) on the runs
     *  that entered {@code arms}: the numbers, or none where they are not known or are still being
     *  asked. */
    private record NumbersAt(InputReads at, ArmsTaken arms, Optional<FormRange> numbers) {}

    /** What {@link #numbersOf} answered of each expression, wherever it was read, for as long as
     *  this is asked: a chain of names is followed once however many expressions read it. The
     *  expression is the node written, and where it was read is told apart by what each name in
     *  it stands for and by the arms the runs it is asked of entered. */
    private final Map<Core, List<NumbersAt>> numbersAsked;

    private FormRange numbersOf(Denotation value, ArmsTaken arms) {
        Core written = Core.withoutStanding(value.value());
        List<NumbersAt> where = numbersAsked.computeIfAbsent(written, _ -> new ArrayList<>());
        for (NumbersAt each : where) {
            if (each.at().equals(value.at()) && each.arms().equals(arms)) {
                return each.numbers().orElse(null);
            }
        }
        int index = where.size();
        where.add(new NumbersAt(value.at(), arms, Optional.empty()));
        FormRange numbers = numbersNotYetAsked(value, arms);
        where.set(index, new NumbersAt(value.at(), arms, Optional.ofNullable(numbers)));
        return numbers;
    }

    private FormRange numbersNotYetAsked(Denotation value, ArmsTaken arms) {
        Core written = Core.withoutStanding(value.value());
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        if (value.at().folded(written, symbols, newtypes).orElse(null) instanceof Long number) {
            return new FormRange(ExactRatio.of(number), ExactRatio.of(number));
        }
        return switch (written) {
            case Core.Read _ -> {
                List<Denotation> given = boundTo(value);
                if (given.isEmpty()) {
                    yield value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)
                            ? rangeOfAPlace(at, arms) : null;
                }
                FormRange hull = null;
                for (Denotation each : given) {
                    FormRange one = numbersOf(each, arms);
                    if (one == null) {
                        yield null;
                    }
                    hull = hull == null ? one : hull.hull(one);
                }
                yield hull;
            }
            case Core.PreservedCall call when AnOperationApplied.of(call) instanceof AnOperationApplied
                    applied -> {
                NumericDomain.Bounds runs = ResultRange.of(
                        DefaultBoundOperationFacts.get().everyBoundOnTheResult(applied.operation()),
                        argument -> applied.argument(argument) instanceof Core handed
                                && value.at().folded(handed, symbols, newtypes).orElse(null)
                                        instanceof Long number
                                ? Optional.of(BigDecimal.valueOf(number)) : Optional.empty());
                yield runs.min() != null && runs.max() != null
                        ? FormRange.ofTheWholeNumbersIn(runs)
                        : written.type() == Type.INT ? heldToAnInt(whatItComesTo(value, arms))
                        : null;
            }
            // A behavior called comes to what its body does, read with what the call hands it.
            case Core.Call _ when AnOperationApplied.of(written) instanceof AnOperationApplied
                    applied && applied.operation() instanceof ValueName.Behavior behavior
                    && !value.at().standsIn(behavior) -> {
                Optional<CalledBody> body =
                        read.rules().declarations().answers().bodyOf(behavior);
                InputReads inside = body.isEmpty() ? null : value.at().calling(behavior,
                        body.get(), applied.args(), newtypes);
                yield inside == null ? null
                        : numbersOf(new Denotation(body.get().body(), inside), arms);
            }
            // A run of names read off one value: a place where the whole run is one, and
            // otherwise read one name at a time.
            case Core.FieldProjection projection -> value.at().pathOf(written, newtypes)
                    instanceof ValuesAt.At(var at) ? rangeOfAPlace(at, arms)
                    : numbersOf(new Denotation(projection.lastAccess(), value.at()), arms);
            case Core.FieldAccess access -> {
                if (value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)) {
                    yield rangeOfAPlace(at, arms);
                }
                // What each construction the value may be gives the field, held to what the rules
                // of its type leave it.
                FormRange left = numbersTheRulesLeave(access);
                List<Denotation> made = valuesItMayBe(new Denotation(access.target(), value.at()));
                if (made == null) {
                    yield left;
                }
                FormRange hull = null;
                for (Denotation each : made) {
                    Core field = fieldOf(each, access.field());
                    FormRange one = field == null ? null
                            : numbersOf(new Denotation(field, each.at()), arms);
                    if (one == null) {
                        yield left;
                    }
                    hull = hull == null ? one : hull.hull(one);
                }
                yield hull == null ? left : left == null ? hull : hull.meet(left);
            }
            case Core.Binary _, Core.Neg _ -> written.type() == Type.INT
                    ? heldToAnInt(whatItComesTo(value, arms)) : null;
            // Either arm a run enters: one no run enters adds nothing.
            case Core.If fork -> {
                FormRange hull = null;
                for (Part arm : partsOf(fork)) {
                    if (arm.arm() < 0) {
                        continue;
                    }
                    ArmsTaken entered = arms.entering(fork, arm.arm(), value.at());
                    if (entered.leaveNoRun(read)) {
                        continue;
                    }
                    FormRange one = numbersOf(new Denotation(arm.expression(), value.at()),
                            entered);
                    if (one == null) {
                        yield null;
                    }
                    hull = hull == null ? one : hull.hull(one);
                }
                yield hull;
            }
            default -> null;
        };
    }

    /** The numbers the rules of the type {@code access} reads a field of leave that field
     *  ({@link DeclaredBounds#ofTheValueReadOff}): a value of the type exists only where they
     *  held, whatever made it. An end they leave open is the end of an {@code Int}, where the
     *  field is one; null where it is anything else and they leave it open. */
    private FormRange numbersTheRulesLeave(Core.FieldAccess access) {
        DeclaredBounds.Range left = DeclaredBounds.ofTheValueReadOff(access, read.rules(),
                read.rules().newtypes(), read.ruleReading());
        if (left == null) {
            return null;
        }
        return access.type() == Type.INT
                ? new FormRange(ExactRatio.of(AN_INT.least()), ExactRatio.of(AN_INT.greatest()))
                        .heldTo(new NumericDomain.Bounds(left.min(), left.max()))
                : FormRange.ofWhatTheRulesLeave(left);
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
        return endsOnlyWhereItsAnswerHasNoPlace(value, new Question(onTheWay));
    }

    private boolean endsOnlyWhereItsAnswerHasNoPlace(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        if (written instanceof Core.LetIn let) {
            question.binding(let.value());
            return endsNoRun(new Denotation(let.value(), value.at()), question)
                    && endsOnlyWhereItsAnswerHasNoPlace(new Denotation(let.body(),
                            value.at().and(let.binder(), let.value())), question);
        }
        return endsOnlyWhereItsOwnAnswerHasNoPlace(written)
                && partsAndNamesEndNoRun(value, question);
    }

    /** Whether what {@code value} is made of, each part on the runs that work it out, and what
     *  each name in it was given, where it was given, end no run. */
    private boolean partsAndNamesEndNoRun(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        for (Part part : partsOf(written)) {
            Question asked = part.arm() >= 0
                    ? question.enteringArm(written, part.arm(), value.at())
                    : Evaluated.runsWhenever(written, part.expression()) ? question
                    : question.notOnEveryRun();
            if (!endsNoRun(new Denotation(part.expression(), value.at()), asked)) {
                return false;
            }
        }
        for (Denotation bound : boundTo(value)) {
            if (!endsNoRun(bound, question.whereItWasBound(bound))) {
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
        return partsOf(written).stream().map(Part::expression).toList();
    }

    /**
     * A part of what a run works out to reach a value, and which arm of the value it is, as
     * {@link Choice} numbers them; {@code arm} is below nought where it is no arm.
     */
    record Part(Core expression, int arm) {}

    /** The parts {@link #whatIsRunWith} lists, each arm with its number. */
    static List<Part> partsOf(Core written) {
        List<Part> parts = new ArrayList<>();
        Core fork = Core.withoutStanding(written);
        if (fork instanceof Core.IfConstructed tested) {
            tested.construct().values().forEach(field -> parts.add(new Part(field.value(), -1)));
        } else {
            for (Evaluated.Step step : Evaluated.inOrder(written)) {
                parts.add(new Part(step.expression(), -1));
            }
        }
        if (fork instanceof Core.If || fork instanceof Core.Match
                || fork instanceof Core.IfConstructed) {
            List<Choice.Arm> arms = Choice.of(fork).arms();
            for (int arm = 0; arm < arms.size(); arm++) {
                parts.add(new Part(arms.get(arm).answers(), arm));
            }
        }
        return parts;
    }
}
