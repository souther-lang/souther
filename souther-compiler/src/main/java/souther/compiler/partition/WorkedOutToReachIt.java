package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.ARowsRun;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BehaviorAnswers;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.CallArguments;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.Choice;
import souther.compiler.check.ClausesInOrder;
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
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalLong;
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
 * more: a rule that told the node elsewhere.
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
        private final Map<Core, Map<ReadAt, WhereItMayEnd>> answered;
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
                         Map<Core, Map<ReadAt, WhereItMayEnd>> answered,
                         FoldedValue.Kept folds,
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

        WhereItMayEnd answerOf(Core written, InputReads at) {
            return answered.getOrDefault(written, Map.of()).get(new ReadAt(at, arms));
        }

        void answer(Core written, InputReads at, WhereItMayEnd answer) {
            answered.computeIfAbsent(written, _ -> new HashMap<>()).put(new ReadAt(at, arms),
                    answer);
        }
    }

    /**
     * What working a value out was answered: that it ends no run, or the expression met on the
     * way whose own working may end one ({@link #ownWorkingEndsNoRun}), where it was read. That
     * expression is the one whose answer made every answer above it what it is, so it is found by
     * the walk that answers whether a run ends and by no other: an expression whose own stop
     * something above it told is not one.
     *
     * @param at the expression, or null where working the value out ends no run
     */
    private record WhereItMayEnd(Denotation at) {

        static final WhereItMayEnd NOWHERE = new WhereItMayEnd(null);

        boolean endsNone() {
            return at == null;
        }
    }

    /** Where an expression was read ({@code at}), on the runs that entered {@code arms}: what an
     *  answer of it is kept by. */
    private record ReadAt(InputReads at, ArmsTaken arms) {}

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
     *
     * <p>Held as the last arm past the ones before it, with how many there are and what they hash
     * to, so that entering one more arm costs the same however deep the way is: a list copied at
     * every arm would cost the square of the depth to reach it, and two lists of arms compared
     * whole would cost the depth on every lookup of an answer.
     */
    private static final class ArmsTaken {

        static final ArmsTaken NONE = new ArmsTaken(null, null, null);

        /** The arm entered last, or null where none is. */
        private final ArmTaken last;
        /** These without the last arm, or null where there are none. */
        private final ArmsTaken past;
        /** What the way to the expression leaves before any arm is entered, or null where that
         *  is what the declarations leave. Held only by the first, which has no arm. */
        private final RegionLeft root;
        private final int depth;
        private final int hash;
        private RegionLeft left;
        /** The reading {@code left} was asked under. */
        private InputReading leftOf;

        private ArmsTaken(ArmTaken last, ArmsTaken past, RegionLeft root) {
            this.last = last;
            this.past = past;
            this.root = root;
            this.depth = past == null ? 0 : past.depth + 1;
            this.hash = past == null ? System.identityHashCode(root)
                    : past.hash * 31 + last.hashCode();
        }

        /** No arm entered, on a way that leaves {@code region}. */
        static ArmsTaken within(SearchRegion region) {
            return new ArmsTaken(null, null, new RegionLeft(region));
        }

        /** Whether no arm is entered and the way leaves what the declarations do. */
        boolean isEmpty() {
            return last == null && root == null;
        }

        /** These, and arm {@code part} of {@code fork} read at {@code at} past them. */
        ArmsTaken entering(Core fork, int part, InputReads at) {
            return new ArmsTaken(new ArmTaken(fork, part, at), this, null);
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
            return !isEmpty() && left(read).holdsNoRow();
        }

        /** What these leave under {@code read}: the one the reading keeps for no arm, or what the
         *  one before keeps for the last arm. Kept with these, but for no arm, which stands for
         *  every reading. */
        private RegionLeft left(InputReading read) {
            if (last == null) {
                return root != null ? root : read.derived(RegionLeft.class,
                        _ -> new RegionLeft(read.quantities().region()));
            }
            if (left == null || leftOf != read) {
                leftOf = read;
                left = past.left(read).past(last, read);
            }
            return left;
        }

        /** The same arms in the same order: compared last arm first, and the arms before it only
         *  where the depth, the hash and that arm agree. */
        @Override
        public boolean equals(Object other) {
            ArmsTaken one = this;
            Object two = other;
            while (one != two) {
                if (!(two instanceof ArmsTaken that) || one.depth != that.depth
                        || one.hash != that.hash || !Objects.equals(one.last, that.last)
                        || one.root != that.root) {
                    return false;
                }
                one = one.past;
                two = that.past;
            }
            return true;
        }

        @Override
        public int hashCode() {
            return hash;
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
            // What entering the arm states is the arm's own condition, whichever arm of an earlier
            // choice the reading that reached it was on: asked untaken, it is one reading of it.
            Proposition stated = WhatConditionsState.of(read)
                    .arm(arm.fork(), arm.part(), arm.at().untaken()).proposition();
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
                               ArmsTaken onTheWay,
                               Map<Core, Map<ReadAt, Optional<WhereAValueComesFrom>>> numbersAsked) {
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

    /**
     * The same, of what only the runs a way leaves {@code region} to work out, with no arm entered
     * yet: what the way states holds on every one of them, so the numbers they hold lie where
     * {@code region} leaves them ({@link ArmsTaken#within}).
     */
    WorkedOutToReachIt within(SearchRegion region) {
        return new WorkedOutToReachIt(read, beyond, closuresApart, toldElsewhere,
                ownStopsSaidOnTheirWays, ArmsTaken.within(region), numbersAsked);
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

    /** The same, each node asked with whatever it applies. */
    static WorkedOutToReachIt asking(InputReading read) {
        return new WorkedOutToReachIt(read, _ -> false, false);
    }

    /**
     * Whether {@code value} itself, apart from what it is made of and what a name in it was given,
     * ends no run: what {@link WhatARunMayEndFor} says of the node, but for a construction, which
     * it leaves unknown because the invariant that may refuse it is the declaration's. A
     * construction ends none where an attempt makes it ({@link InputReads#builtByAnAttempt}),
     * where the discharge check proved every clause of it under what holds where it is made
     * ({@link BehaviorAnswers#shownToHold}), and where its clauses fold to true over what it is
     * handed ({@link #aConstructionEndsNoRun}).
     * Anything else is gotten past where a run of a row gets past it ({@link ARowsRun}).
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
        BehaviorAnswers answers = read.rules().declarations().answers();
        return closuresApart
                ? ARowsRun.completionOf(written, answers) instanceof GetsPast.Always
                : ARowsRun.getsPastWhole(written, answers);
    }

    /**
     * Whether {@code value} is an operation that ends a run on its divisor alone, only where that
     * is nought, as the operation's owner says ({@link Pullback#theDivisorItAloneStopsOn}), and
     * the numbers the divisor comes to ({@link #numbersOf}) leave nought out, whether it is one
     * number, as in {@code Int.floorMod(x, 7)}, or a range a declaration holds it to.
     */
    private boolean stopsOnlyOnAnOperandThatIsNotNought(Denotation value) {
        Core operand = Pullback.theDivisorItAloneStopsOn(value.value());
        if (operand == null) {
            return false;
        }
        FormRange numbers = numbersOf(new Denotation(operand, value.at()));
        return numbers != null && !numbers.holds(ExactRatio.ZERO);
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
        return whereARunMayEnd(value).isEmpty();
    }

    /** Where working out {@code value}, and what each name read in it was given, may end a run:
     *  the expression whose own working may end one; none where it ends none. */
    Optional<Denotation> whereARunMayEnd(Denotation value) {
        return Optional.ofNullable(whereItMayEnd(value, new Question(onTheWay)).at());
    }

    /** Where working out {@code closure} where {@code call} applies it may end a run, asked with
     *  what the call hands it ({@link #closuresHeldOverTheirElements}); none where it ends none. */
    Optional<Denotation> whereARunMayEndWhereApplied(Denotation call, Core.Block closure) {
        Question question = new Question(true, onTheWay);
        return Optional.ofNullable(whereItMayEnd(new Denotation(closure, call.at()),
                question.applying(closuresHeldOverTheirElements(call, question))).at());
    }

    private boolean endsNoRun(Denotation value, Question question) {
        return whereItMayEnd(value, question).endsNone();
    }

    /**
     * Whether working out {@code value} ends no run, and where not, the expression whose own
     * working may end one ({@link WhereItMayEnd}). The one walk that answers whether a run ends:
     * every reader of it is answered here, whichever of the two it reads.
     */
    private WhereItMayEnd whereItMayEnd(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        if (question.heldWhereApplied.contains(written)) {
            return WhereItMayEnd.NOWHERE;
        }
        WhereItMayEnd known = question.answerOf(written, value.at());
        if (known != null) {
            return known;
        }
        WhereItMayEnd answer = worksOutWithoutEndingARun(value, question);
        question.answer(written, value.at(), answer);
        return answer;
    }

    /** Asked of what {@code value} is made of first, so that what another reading tells is only
     *  ever the least of it that may end a run: telling a value names what it reads. */
    private WhereItMayEnd worksOutWithoutEndingARun(Denotation value, Question question) {
        WhereItMayEnd itself = worksOutOfItselfWithoutEndingARun(value, question);
        return itself.endsNone() || toldElsewhere.test(value) || question.tells(value)
                ? WhereItMayEnd.NOWHERE : itself;
    }

    private WhereItMayEnd worksOutOfItselfWithoutEndingARun(Denotation value,
                                                            Question question) {
        // Past arms no run enters together, nothing is worked out on any run.
        if (question.arms.leaveNoRun(read)) {
            return WhereItMayEnd.NOWHERE;
        }
        Core written = Core.withoutStanding(value.value());
        if (closuresApart && written instanceof Core.Block closure) {
            return whereItMayEnd(new Denotation(closure.body(), value.at()),
                    question.notOnEveryRun());
        }
        if (written instanceof Core.LetIn let) {
            question.binding(let.value());
            WhereItMayEnd given = whereItMayEnd(new Denotation(let.value(), value.at()), question);
            return !given.endsNone() ? given : whereItMayEnd(new Denotation(let.body(),
                    value.at().and(let.binder(), let.value())), question);
        }
        // Written in a value that was built, whatever is inside it: the build ran all of it.
        if (written instanceof Core.Construct made && read.rules().declarations().answers()
                .builtWhereItsModuleIsBuilt(read.rules().symbols().module(), made.pos())) {
            return WhereItMayEnd.NOWHERE;
        }
        // A reference to a value is run as the value is defined, which no part of this node says.
        if (written instanceof Core.MaterialisedValue) {
            Denotation defined = value.at().taken(written);
            return defined == null ? new WhereItMayEnd(value)
                    : whereItMayEnd(defined, question.whereItWasBound(defined));
        }
        if (question.byTheNumbers) {
            Set<Core> held = closuresHeldOverTheirElements(value, question);
            if (!held.isEmpty()) {
                Question applying = question.applying(held);
                return !ownWorkingEndsNoRun(value, applying) ? new WhereItMayEnd(value)
                        : whereThePartsAndNamesMayEnd(value, applying);
            }
        }
        return !ownWorkingEndsNoRun(value, question) ? new WhereItMayEnd(value)
                : whereThePartsAndNamesMayEnd(value, question);
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
        Long most = mostElementsOf(container, where);
        return new Worth(added, rangesOfTheElements(where, element, answer.position(), container,
                added.aliases(), most), answer.body(), most);
    }

    /**
     * How many elements {@code container}, read in {@code where}, holds at most: as many as the
     * walk of it writes out less those there on no run ({@link WrittenOutElements#mostOf}),
     * through the names, {@code let}s and helpers it stands at and the operations that keep a piece
     * of each element of another — or, where it is not written out, the most a list holds.
     *
     * <p>A bound on how many elements a total or a walk is handed and nothing more: what a run
     * works out to reach the container is asked of the parts and names it is written with.
     */
    private Long mostElementsOf(Core container, InputReads where) {
        OptionalLong written = WrittenOutElements.mostOf(new Denotation(container, where),
                read.rules().symbols(), read.rules().newtypes());
        return written.isPresent() ? Long.valueOf(written.getAsLong())
                : RepresentationBounds.mostElements();
    }

    /**
     * What a path of the element handed on {@code element} comes to, read in {@code where}: what
     * it comes to at whichever place the element is the value at ({@link #placesTheElementIsAt}),
     * held to what every test that kept it states; the code point of a string, from nought to the
     * last there is; what the rules of the type a field is read off leave the field
     * ({@link #numbersTheRulesLeave}), whatever made the value; or, where it is the position handed
     * on {@code position}, from nought to one below {@code most}. Null where it is none of these.
     */
    private Function<Core, FormRange> rangesOfTheElements(
            InputReads where, BindingId element, BindingId position, Core container,
            Map<BindingId, Core> aliases, Long most) {
        DeclarationNewtypes newtypes = read.rules().newtypes();
        NumericTerm aCodePoint = InputNumber.aCodePointListedBy(container, read.domain(), where,
                read.rules());
        List<TermPath> places = placesTheElementIsAt(where, element, container);
        List<Proposition> stated = places.isEmpty() ? List.of()
                : whatEachTestThatKeptItStates(new Denotation(container, where));
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
            if (!places.isEmpty()) {
                return rangeAtEachOf(place, places, stated);
            }
            if (place.steps().isEmpty() && aCodePoint != null) {
                return FormRange.endsOf(aCodePoint, read);
            }
            return Core.withoutStanding(path) instanceof Core.FieldAccess access
                    ? numbersTheRulesLeave(access) : null;
        };
    }

    /**
     * The places the element handed on {@code element} is, on every run, the value at one of:
     * where every element of {@code container} stands ({@link InputReads#everyElementAt}); where
     * it stands though it is some of them and not every one, as an element a filter, a
     * {@code take} or a reordering keeps is ({@link InputReads#elementAt}); or where each element
     * of the list written out stands ({@link #placesOfTheElementsWrittenOut}). None where it is
     * none of these.
     *
     * <p>A place a value only may stand at is none of these: among several cases, one standing at
     * no place adds none, and the value may be that one.
     */
    private List<TermPath> placesTheElementIsAt(InputReads where, BindingId element,
                                                Core container) {
        DeclarationNewtypes newtypes = read.rules().newtypes();
        switch (where.everyElementAt(element, newtypes)) {
            case ValuesHeld.At(TermPath at) -> {
                return List.of(at);
            }
            case ValuesHeld.MayStandAt(List<TermPath> among) -> {
                return among;
            }
            case ValuesHeld.NotAPosition _ -> { }
        }
        if (where.elementAt(element, newtypes) instanceof ValuesAt.At(TermPath at)) {
            return List.of(at);
        }
        List<TermPath> written = placesOfTheElementsWrittenOut(new Denotation(container, where));
        return written == null ? List.of() : written;
    }

    /**
     * The place each element of {@code container} stands at, as the list is written out
     * ({@link #elementsWrittenOut}), the ones a test may drop as well: one dropped on some run is
     * one another run keeps. Null where it is no list written out, holds none, or one of them
     * stands at no one place.
     */
    private List<TermPath> placesOfTheElementsWrittenOut(Denotation container) {
        List<Denotation> elements = elementsWrittenOut(container);
        if (elements == null || elements.isEmpty()) {
            return null;
        }
        List<TermPath> places = new ArrayList<>();
        for (Denotation each : elements) {
            if (!(each.at().pathOf(Core.withoutStanding(each.value()), read.rules().newtypes())
                    instanceof ValuesAt.At(var at))) {
                return null;
            }
            places.add(at);
        }
        return places;
    }

    /**
     * What {@code place} comes to at whichever of {@code among} the element stands at, each held
     * to what every test in {@code stated} that kept the element says of it
     * ({@link #heldByWhatItStates}): the hull of what it comes to at each, or null where one of
     * them comes to nothing known. A test states something of the one place its parameter stands
     * at, and of every other it says nothing.
     */
    private FormRange rangeAtEachOf(ElementProjection place, List<TermPath> among,
                                    List<Proposition> stated) {
        FormRange hull = null;
        for (TermPath each : among) {
            TermPath at = place.from(each);
            FormRange one = rangeOfAPlace(at, ArmsTaken.NONE);
            NumericTerm term = new NumericTerm.ValueOf(at);
            for (Proposition test : stated) {
                one = heldByWhatItStates(one, term, test);
            }
            if (one == null) {
                return null;
            }
            hull = hull == null ? one : hull.hull(one);
        }
        return hull;
    }

    /**
     * What each test that kept an element of {@code container} states of the element it was
     * handed: the test of the operation that made the container, where it keeps the elements of
     * another a test holds of, and so on into the container it took them from, through every
     * operation whose answer holds some of the very elements it was handed — a {@code take}, a
     * reordering ({@link InputReads#argumentWhoseElementsItHolds}) — as far as one keeps them.
     * Every element kept on the way is one each of those tests held of, which is what the library
     * says such an operation keeps. A test that is no closure of one value states nothing here,
     * and the container it took its elements from is followed all the same. A name a container is
     * given is read as the one value it was given.
     *
     * <p>Each is of the place the elements of the container it walks stand at, which an element
     * kept on the way stands at too, where the reading takes the parameter of the test as the
     * element it is handed; a statement of any other value says nothing of that place and is
     * passed over where it is read ({@link #heldByWhatItStates}).
     */
    private List<Proposition> whatEachTestThatKeptItStates(Denotation container) {
        List<Proposition> out = new ArrayList<>();
        Set<Core> walked = Collections.newSetFromMap(new IdentityHashMap<>());
        Denotation at = theOneValueOf(container);
        while (at != null && Core.withoutStanding(at.value()) instanceof Core.PreservedCall call
                && walked.add(call)) {
            BoundOperationFacts.Kept keeps =
                    DefaultBoundOperationFacts.get().keepsWhereItHolds(call.operation());
            DeclaredArgument source = keeps != null ? keeps.source()
                    : InputReads.argumentWhoseElementsItHolds(call.operation());
            if (source == null) {
                break;
            }
            if (keeps != null && Core.withoutStanding(CallArguments.of(keeps.closure(), call))
                    instanceof Core.Block test && test.params().size() == 1) {
                out.add(WhatConditionsState.of(read).truth(test.body(), at.at(), read)
                        .proposition());
            }
            at = theOneValueOf(new Denotation(CallArguments.of(source, call), at.at()));
        }
        return out;
    }

    /** {@code value}, or the one value it was given where it is a name given one, and so on: the
     *  name itself where it was given none, as a parameter is, and null where it stands for
     *  several. */
    private Denotation theOneValueOf(Denotation value) {
        Denotation at = value;
        Set<Core> walked = Collections.newSetFromMap(new IdentityHashMap<>());
        while (Core.withoutStanding(at.value()) instanceof Core.Read name && walked.add(name)) {
            List<Denotation> given = boundTo(at);
            if (given.size() != 1) {
                return given.isEmpty() ? at : null;
            }
            at = given.getFirst();
        }
        return at;
    }

    /**
     * {@code range}, the numbers {@code term} comes to, held to what {@code stated} holding says
     * of it alone: each relation of a number times it against a number, and every part of
     * statements held together. As it is where the statement says nothing such of it, and null
     * where no number of it meets the statement.
     */
    private static FormRange heldByWhatItStates(FormRange range, NumericTerm term,
                                                Proposition stated) {
        if (range == null) {
            return null;
        }
        return switch (stated) {
            case Proposition.All(var parts, var _, var _) -> {
                FormRange held = range;
                for (Proposition part : parts) {
                    held = heldByWhatItStates(held, term, part);
                    if (held == null) {
                        yield null;
                    }
                }
                yield held;
            }
            case Proposition.Compared(Relation.Affine affine, boolean holds, var _, var _)
                    // A relation of one number of the input, weighed against nought.
                    when affine.form().coefs().size() == 1
                    && affine.form().coefs().keySet().iterator().next()
                            instanceof DecisionAtom.OfTheInput(NumericTerm weighed, var _)
                    && weighed.equals(term) -> {
                // weight * term + constant against nought, which is term against what the
                // constant comes to over the weight: a relation faces one way, so the weight of
                // its one term is above nought.
                ExactRatio weight = affine.form().coefs().values().iterator().next();
                Rel met = holds ? affine.proposition() : affine.proposition().denied();
                yield affine.form().constant().negated().dividedBy(weight)
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio level)
                        ? range.heldTo(met, level)
                        : range;
            }
            default -> range;
        };
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
        Long most = step == null ? null : mostElementsOf(walk.container(), where);
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
        FormRange total = whatATotalComesTo(value);
        return total != null && total.liesWithin(AN_INT.least(), AN_INT.greatest());
    }

    /**
     * The numbers {@code value}, a total of whole numbers held to an {@code Int}
     * ({@link GetsPast.WhereTheTotalFits}), comes to as it is added up, before its type holds it:
     * from what each element comes to times as many as there may be, and nought, or the sum of a
     * list written out. Null where it is no such total, or that is not known.
     */
    FormRange whatATotalComesTo(Denotation value) {
        if (!(Core.withoutStanding(value.value()) instanceof Core.PreservedCall call)
                || !(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(call)
                        instanceof GetsPast.WhereTheTotalFits(int list))
                || list >= call.args().size()) {
            return null;
        }
        Denotation listed = new Denotation(call.args().get(list), value.at());
        Worth each = whatEachElementIsWorth(listed, new Question(onTheWay));
        if (each != null) {
            FormRange one = each.added().answerHeldWithin(each.rangeOf(), AN_INT.least(),
                    AN_INT.greatest());
            if (one == null || each.most() == null) {
                return null;
            }
            FormRange total = FormRange.combined(BinOp.MUL, one,
                    new FormRange(ExactRatio.ZERO, ExactRatio.of(each.most())));
            return total == null ? null
                    : total.hull(new FormRange(ExactRatio.ZERO, ExactRatio.ZERO));
        }
        return theSumOfAListWrittenOut(listed);
    }

    /** The sum of {@code listed}, a list written out, every element there and a number the fold
     *  works out; null where it is not that. */
    private FormRange theSumOfAListWrittenOut(Denotation listed) {
        if (!(WrittenOutElements.of(listed, read.rules().symbols(), read.rules().newtypes())
                instanceof WrittenOutElements.Walked.Each written)) {
            return null;
        }
        BigInteger sum = BigInteger.ZERO;
        for (ReadMeaning.Occurrence each : written.asWritten()) {
            Denotation element = each.value();
            if (!each.keptWhere().isEmpty()
                    || !(element.at().folded(element.value(), read.rules().symbols(),
                            read.rules().newtypes()).orElse(null) instanceof Long number)) {
                return null;
            }
            sum = sum.add(BigInteger.valueOf(number));
        }
        return new FormRange(ExactRatio.of(sum), ExactRatio.of(sum));
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
        return whereARunMayEndWhereItWasPassedOver(value).isEmpty();
    }

    /**
     * The expression whose own working may end a run working out {@code value}, which a reading
     * passed over, where it was read; none where working it out ends no run, which is
     * {@link #endsNoRunWhereItWasPassedOver}. Found by the walk that answers that, so it is the
     * expression the answer rests on: the first of them the walk met, and not every one there is.
     */
    Optional<Denotation> whereARunMayEndWhereItWasPassedOver(Denotation value) {
        return Optional.ofNullable(whereItMayEnd(value, new Question(true, onTheWay)).at());
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
        return whereAStopIsLeftUntoldWhereItWasPassedOver(value, tells).isEmpty();
    }

    /** The expression whose own stop is left untold working out {@code value}, where it was
     *  read, as {@link #whereARunMayEndWhereItWasPassedOver} finds it; none where every stop
     *  there is told ({@link #endsNoRunUntoldWhereItWasPassedOver}). */
    Optional<Denotation> whereAStopIsLeftUntoldWhereItWasPassedOver(Denotation value,
                                                                    Predicate<Denotation> tells) {
        return Optional.ofNullable(whereItMayEnd(value,
                new Question(true, tells, ownStopsSaidOnTheirWays, onTheWay)).at());
    }

    /**
     * Where working out {@code value}, which a reading passed over, leaves a stop unsaid; none
     * where every stop a run may come to there is none, or one the analysis says on each way
     * ({@link #besideTheStopsSaidOnTheirWays}). Not whether a run ends, which a stop said
     * elsewhere does not answer.
     */
    Optional<Denotation> whereAStopIsLeftUnsaidWhereItWasPassedOver(Denotation value) {
        return Optional.ofNullable(whereItMayEnd(value,
                new Question(true, null, ownStopsSaidOnTheirWays, onTheWay)).at());
    }

    /**
     * Whether {@code value} is a whole number worked out of operands that come to numbers
     * ({@link #numbersOf}), on the runs that entered {@code arms}, by an operation that ends a run
     * only past an {@code Int} ({@link #whatItComesTo}), and it takes them to no number past one.
     */
    private boolean anOperatorWithinAnInt(Denotation value, ArmsTaken arms) {
        FormRange range = Core.withoutStanding(value.value()).type() == Type.INT
                ? whatItComesTo(value, arms) : null;
        return range != null && range.liesWithin(AN_INT.least(), AN_INT.greatest());
    }

    /**
     * The numbers {@code value} works out, on the runs that entered {@code arms}, from the numbers
     * its operands come to, before its type holds them: a sum, a difference, a product or a
     * negation, a number rounded to a whole one ({@link GetsPast.WhereTheRoundedNumberFits}), or
     * what a call of the library answers in each case it is defined in ({@link Choice#casesOf})
     * where all it ends a run for is that answer having no place. Null where it is none of these
     * or that is not known.
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
            case Core.PreservedCall call when WhatARunMayEndFor
                    .completionApartFromTheClosuresWrittenAtIt(call)
                    instanceof GetsPast.WhereTheRoundedNumberFits(int rounded) ->
                    rounded < call.args().size()
                            ? FormRange.roundedEitherWay(operand.apply(call.args().get(rounded)))
                            : null;
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

    /** Every element of {@code list} where it is a list written out, each as written, or null
     *  where it is none ({@link WrittenOutElements#of}). */
    private List<Denotation> elementsWrittenOut(Denotation list) {
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
     * ({@link ResultRange}), what an operation makes of its operands' numbers, an element of a
     * container a call answered and an arm opened, what a walk keeping its seed or an element
     * comes to, and any arm of a choice, each on the runs that enter it with the names it binds.
     * Where none of these says, an {@code Int} comes to what an {@code Int} holds on a run that
     * got it. Each expression is asked once
     * ({@link #numbersAsked}), where it is written, as an expression {@link #endsNoRun} meets is.
     * On the runs that entered the arms this is asked past ({@link #onTheArm}).
     */
    FormRange numbersOf(Denotation value) {
        return numbersOf(value, onTheWay);
    }

    /** Where the numbers {@link #numbersOf} answers of {@code value} come from, which a way to
     *  it may narrow ({@link WhereAValueComesFrom}); null where they are not known. */
    WhereAValueComesFrom originOf(Denotation value) {
        return originOf(value, onTheWay);
    }

    /**
     * Each way a row can make {@code value} come to a number of the input, as far as it is known
     * ({@link Attainment}): a number written, what a place holds, what a name was given, and the
     * element a call answers where that is one a row makes the only one, or the greatest or least
     * of a list written out. None where the value is anything else: the numbers it may come to
     * ({@link #originOf}) say none of them is one a row gets. Some left unmade where a rule
     * says how and the ways are more than a stop is looked for by ({@link Attainments}).
     */
    Attainments attainmentsOf(Denotation value) {
        return attainmentsOf(value, onTheWay);
    }

    /**
     * What {@code value} is where it is a {@code let}: its body, with the name the {@code let}
     * gives bound to the value it gives it, as a walk of the body binds it. A {@code let} comes to
     * what its body comes to. Null where it is no {@code let}, or gives a build of a value, whose
     * template is read where the value is defined.
     */
    private static Denotation inTheBodyOfALet(Denotation value) {
        return Core.withoutStanding(value.value()) instanceof Core.LetIn let
                && !(Core.withoutStanding(let.value()) instanceof Core.MaterialisedValue)
                ? new Denotation(let.body(), value.at().and(let.binder(), let.value())) : null;
    }

    private Attainments attainmentsOf(Denotation value, ArmsTaken arms) {
        Core written = Core.withoutStanding(value.value());
        if (inTheBodyOfALet(value) instanceof Denotation body) {
            return attainmentsOf(body, arms);
        }
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        if (value.at().folded(written, symbols, newtypes).orElse(null) instanceof Long number) {
            return Attainments.of(List.of(Attainment.always(
                    LinearForm.constant(ExactRatio.of(number)))));
        }
        if (written instanceof Core.FieldAccess || written instanceof Core.FieldProjection) {
            return value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)
                    ? attainmentsAtAPlace(at, arms) : Attainments.NONE;
        }
        if (written instanceof Core.PreservedCall) {
            return attainmentsOfAWalk(value, arms);
        }
        if (!(written instanceof Core.Read name)) {
            return Attainments.NONE;
        }
        List<Denotation> given = boundTo(value);
        if (given.isEmpty()) {
            return value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)
                    ? attainmentsAtAPlace(at, arms)
                    : attainmentsOfAnOpenedElement(name, value.at(), arms);
        }
        return given.size() == 1 ? attainmentsOf(given.getFirst(), arms) : Attainments.NONE;
    }

    /**
     * How a row makes a walk from a seed come to a number, where it walks a container of the
     * input and the step answers the element it is handed or what it carried
     * ({@link #answersTheElementOrWhatItCarried}): over none, the seed, whatever the step is; over
     * one, what the step answers of the seed and that element. A walk over more comes to what the
     * step makes of each in turn, which is not said here.
     */
    private Attainments attainmentsOfAWalk(Denotation value, ArmsTaken arms) {
        Denotation met = value.at().denotes(Core.withoutStanding(value.value()),
                read.rules().symbols(), read.rules().newtypes());
        SeededWalk walk = met == null ? null : SeededWalk.of(met.value(), closure ->
                Core.withoutStanding(closure) instanceof Core.Block block ? block : null);
        if (walk == null || !(met.at().everyElementOf(walk.container(), read.rules().newtypes())
                instanceof ValuesHeld.At(TermPath element))
                || !AValueOfTheInput.ofTheOnlyElement(element)
                || !answersTheElementOrWhatItCarried(walk.step().body(),
                        walk.element().binding(), walk.accumulator().binding())) {
            return Attainments.NONE;
        }
        NumericTerm count = AValueOfTheInput.howMany(
                element.prefix(element.steps().size() - 1), read);
        if (count == null) {
            return Attainments.NONE;
        }
        Attainments seeds = attainmentsOf(new Denotation(walk.seed(), met.at()), arms);
        if (seeds.leftUnmade()) {
            return Attainments.TOO_MANY;
        }
        Attainments.Builder out = new Attainments.Builder();
        holdingTheCount(seeds, count, ExactRatio.ZERO, out);
        Attainment theElement = Attainment.always(LinearForm.atom(
                new NumericTerm.ValueOf(element)));
        holdingTheCount(answersOfAStep(walk.step().body(), new AStepOverOne(
                walk.element().binding(), walk.accumulator().binding(), seeds, theElement)),
                count, ExactRatio.ONE, out);
        return out.build();
    }

    /** Each of {@code of}, for the rows where the list {@code count} counts holds {@code size},
     *  made into {@code out}. */
    private static void holdingTheCount(Attainments of, NumericTerm count, ExactRatio size,
                                        Attainments.Builder out) {
        out.noting(of);
        TakenConstraint.Affine exactly = new TakenConstraint.Affine(
                LinearForm.atomMinusConstant(count, size), Rel.EQ);
        for (Attainment each : of.ways()) {
            List<TakenConstraint.Affine> holding = new ArrayList<>(each.holding());
            holding.add(exactly);
            if (!out.add(new Attainment(each.form(), holding))) {
                return;
            }
        }
    }

    /**
     * What a step answers of the seed {@code carried} stands for and the element {@code element}
     * stands for: the one it answers by name, or either of the arms of a choice, each with what
     * the choice leaves it — the comparison of two such answers, or its denial — as what a row
     * meets for the step to answer it. Nothing where a comparison is of anything else.
     */
    private static Attainments answersOfAStep(Core body, AStepOverOne step) {
        return switch (Core.withoutStanding(body)) {
            case Core.Read name -> step.element().equals(name.binding())
                    ? Attainments.of(List.of(step.theElement()))
                    : step.carried().equals(name.binding()) ? step.seeds() : Attainments.NONE;
            case Core.If fork -> answersOfAChoice(fork, step);
            default -> Attainments.NONE;
        };
    }

    /** What a step walks one element with: the names it is handed the element and what it
     *  carried by, and how a row makes each of them a number. */
    private record AStepOverOne(BindingId element, BindingId carried, Attainments seeds,
                                Attainment theElement) {}

    /** What either arm of {@code fork} answers, each where a row meets what the comparison it is
     *  decided by states, or its denial. None where it is decided by anything else. */
    private static Attainments answersOfAChoice(Core.If fork, AStepOverOne step) {
        if (!(Core.withoutStanding(fork.cond()) instanceof Core.Binary comparison)
                || !comparison.op().compares()) {
            return Attainments.NONE;
        }
        Rel rel = comparison.op().relation();
        Attainments lefts = answersOfAStep(comparison.left(), step);
        Attainments rights = answersOfAStep(comparison.right(), step);
        Attainments.Builder out = new Attainments.Builder();
        out.noting(lefts);
        out.noting(rights);
        for (Attainment left : lefts.ways()) {
            for (Attainment right : rights.ways()) {
                LinearForm<NumericTerm> apart = left.form().minus(right.form()).orNull();
                if (apart == null) {
                    continue;
                }
                List<TakenConstraint.Affine> holding = new ArrayList<>(left.holding());
                holding.addAll(right.holding());
                // Made until one is refused, and no sooner: that the room is used up says
                // nothing of whether there is another way to make.
                if (!answeredWhere(fork.then(), new TakenConstraint.Affine(apart, rel), holding,
                        step, out)
                        || !answeredWhere(fork.els(),
                                new TakenConstraint.Affine(apart, rel.denied()), holding, step,
                                out)) {
                    return out.build();
                }
            }
        }
        return out.build();
    }

    /** What {@code arm} answers where a row meets {@code taken} and {@code before}, made into
     *  {@code out}: false where one of them was refused for want of room. */
    private static boolean answeredWhere(Core arm, TakenConstraint.Affine taken,
                                         List<TakenConstraint.Affine> before, AStepOverOne step,
                                         Attainments.Builder out) {
        Attainments answers = answersOfAStep(arm, step);
        out.noting(answers);
        for (Attainment answer : answers.ways()) {
            List<TakenConstraint.Affine> holding = new ArrayList<>(answer.holding());
            holding.addAll(before);
            holding.add(taken);
            if (!out.add(new Attainment(answer.form(), holding))) {
                return false;
            }
        }
        return true;
    }

    /** What {@code place} holds, where that is known ({@link #atAPlace}). */
    private Attainments attainmentsAtAPlace(TermPath place, ArmsTaken arms) {
        return atAPlace(place, arms) == null ? Attainments.NONE
                : Attainments.of(List.of(Attainment.always(
                        LinearForm.atom(new NumericTerm.ValueOf(place)))));
    }

    /** The element an arm opened over the answer of a call, as {@link #originOfAnOpenedElement}
     *  reads it. */
    private Attainments attainmentsOfAnOpenedElement(Core.Read name, InputReads at,
                                                     ArmsTaken arms) {
        InputReads.ElementOpened opened = at.elementOpenedBy(name.binding());
        if (opened == null || !(AnOperationApplied.of(Core.withoutStanding(opened.call().value()))
                instanceof AnOperationApplied answered)) {
            return Attainments.NONE;
        }
        var facts = DefaultBoundOperationFacts.get();
        var container = facts.answersAnElementOf(answered.operation());
        Core of = container == null ? null : answered.argument(container);
        if (of == null) {
            return Attainments.NONE;
        }
        BoundOperationFacts.Extremity extremity = facts.answersAnExtremeElementOf(
                answered.operation());
        return attainmentsOfAnElementOf(new Denotation(of, opened.call().at()), arms,
                extremity == null ? null : extremity.end());
    }

    /**
     * How a row makes the element a call answered of {@code container} come to a number, where
     * {@code end} says which end of the elements it is, and null where it is none.
     *
     * <p>Of a list written out: the end is element {@code i} where no other is past it, that
     * comparison being what makes the run answer it; with no end, only a list of one element has
     * one to answer. Of the elements at a place, the number a row's only element holds, which
     * {@link AValueOfTheInput} asks of a list of one element and no other.
     */
    private Attainments attainmentsOfAnElementOf(Denotation container, ArmsTaken arms,
                                                 BoundOperationFacts.End end) {
        List<Denotation> written = elementsWrittenOut(container);
        if (written == null) {
            return switch (container.at().everyElementOf(container.value(),
                    read.rules().newtypes())) {
                case ValuesHeld.At(TermPath at) -> attainmentsAtAPlace(at, arms);
                case ValuesHeld.MayStandAt _, ValuesHeld.NotAPosition _ -> Attainments.NONE;
            };
        }
        // Each way is made of a comparison with every other, so the elements are no more than the
        // ways there is room for ({@link Attainments#MOST}), before any is made.
        if (written.size() > Attainments.MOST) {
            return Attainments.TOO_MANY;
        }
        List<Attainment> each = new ArrayList<>(written.size());
        for (Denotation element : written) {
            Attainments one = attainmentsOf(element, arms);
            if (one.leftUnmade()) {
                return Attainments.TOO_MANY;
            }
            if (one.ways().size() != 1) {
                return Attainments.NONE;
            }
            each.add(one.ways().getFirst());
        }
        if (end == null) {
            return each.size() == 1 ? Attainments.of(each) : Attainments.NONE;
        }
        Attainments.Builder out = new Attainments.Builder();
        for (int chosen = 0; chosen < each.size(); chosen++) {
            List<TakenConstraint.Affine> holding = new ArrayList<>(each.get(chosen).holding());
            for (int other = 0; other < each.size(); other++) {
                if (other == chosen) {
                    continue;
                }
                holding.addAll(each.get(other).holding());
                LinearForm<NumericTerm> past = end == BoundOperationFacts.End.GREATEST
                        ? each.get(chosen).form().minus(each.get(other).form()).orNull()
                        : each.get(other).form().minus(each.get(chosen).form()).orNull();
                if (past == null) {
                    return Attainments.NONE;
                }
                holding.add(new TakenConstraint.Affine(past, Rel.GE));
            }
            out.add(new Attainment(each.get(chosen).form(), holding));
        }
        return out.build();
    }

    /** What {@link #originOf} answered of each expression, wherever it was read, for as long as
     *  this is asked: a chain of names is followed once however many expressions read it. The
     *  expression is the node written, and where it was read is told apart by what each name in
     *  it stands for and by the arms the runs it is asked of entered. None where the numbers are
     *  not known or are still being asked. The numbers and where they come from are one answer,
     *  asked once. */
    private final Map<Core, Map<ReadAt, Optional<WhereAValueComesFrom>>> numbersAsked;

    private FormRange numbersOf(Denotation value, ArmsTaken arms) {
        WhereAValueComesFrom origin = originOf(value, arms);
        FormRange range = origin == null ? null : origin.range();
        return range == null && Core.withoutStanding(value.value()).type() == Type.INT
                ? new FormRange(ExactRatio.of(AN_INT.least()), ExactRatio.of(AN_INT.greatest()))
                : range;
    }

    private WhereAValueComesFrom originOf(Denotation value, ArmsTaken arms) {
        Core written = Core.withoutStanding(value.value());
        Map<ReadAt, Optional<WhereAValueComesFrom>> where =
                numbersAsked.computeIfAbsent(written, _ -> new HashMap<>());
        ReadAt at = new ReadAt(value.at(), arms);
        Optional<WhereAValueComesFrom> known = where.get(at);
        if (known != null) {
            return known.orElse(null);
        }
        where.put(at, Optional.empty());
        WhereAValueComesFrom origin = originNotYetAsked(value, arms);
        where.put(at, Optional.ofNullable(origin));
        return origin;
    }

    private WhereAValueComesFrom originNotYetAsked(Denotation value, ArmsTaken arms) {
        Core written = Core.withoutStanding(value.value());
        if (inTheBodyOfALet(value) instanceof Denotation body) {
            return originOf(body, arms);
        }
        Symbols symbols = read.rules().symbols();
        DeclarationNewtypes newtypes = read.rules().newtypes();
        if (value.at().folded(written, symbols, newtypes).orElse(null) instanceof Long number) {
            return new WhereAValueComesFrom.Fixed(new FormRange(ExactRatio.of(number),
                    ExactRatio.of(number)));
        }
        return switch (written) {
            case Core.Read name -> {
                List<Denotation> given = boundTo(value);
                if (given.isEmpty()) {
                    yield value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)
                            ? atAPlace(at, arms)
                            : originOfAnOpenedElement(name, value.at(), arms);
                }
                List<WhereAValueComesFrom> candidates = new ArrayList<>();
                for (Denotation each : given) {
                    WhereAValueComesFrom one = originOf(each, arms);
                    if (one == null) {
                        yield null;
                    }
                    candidates.add(one);
                }
                yield WhereAValueComesFrom.oneOf(candidates);
            }
            case Core.PreservedCall _ when originOfAWalkKept(value, arms)
                    instanceof WhereAValueComesFrom kept -> kept;
            case Core.PreservedCall _ when whatATotalComesTo(value) instanceof FormRange total ->
                    derived(heldToAnInt(total));
            case Core.PreservedCall call when AnOperationApplied.of(call) instanceof AnOperationApplied
                    applied -> {
                NumericDomain.Bounds runs = ResultRange.of(
                        DefaultBoundOperationFacts.get().everyBoundOnTheResult(applied.operation()),
                        argument -> applied.argument(argument) instanceof Core handed
                                && value.at().folded(handed, symbols, newtypes).orElse(null)
                                        instanceof Long number
                                ? Optional.of(BigDecimal.valueOf(number)) : Optional.empty());
                yield derived(runs.min() != null && runs.max() != null
                        ? FormRange.ofTheWholeNumbersIn(runs)
                        : written.type() == Type.INT ? heldToAnInt(whatItComesTo(value, arms))
                        : null);
            }
            // A run of names read off one value: a place where the whole run is one, and
            // otherwise read one name at a time.
            case Core.FieldProjection projection -> {
                if (value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)) {
                    yield atAPlace(at, arms);
                }
                WhereAValueComesFrom ofTheElements =
                        originOfAPathOfTheElements(written, value.at(), arms, null);
                yield ofTheElements != null ? ofTheElements
                        : originOf(new Denotation(projection.lastAccess(), value.at()), arms);
            }
            case Core.FieldAccess access -> {
                if (value.at().pathOf(written, newtypes) instanceof ValuesAt.At(var at)) {
                    yield atAPlace(at, arms);
                }
                // What each construction the value may be gives the field, held to what the rules
                // of its type leave it.
                FormRange left = numbersTheRulesLeave(access);
                WhereAValueComesFrom ofTheElements =
                        originOfAPathOfTheElements(written, value.at(), arms, left);
                if (ofTheElements != null) {
                    yield ofTheElements;
                }
                List<Denotation> made = valuesItMayBe(new Denotation(access.target(), value.at()));
                if (made == null) {
                    yield derived(left);
                }
                FormRange hull = null;
                for (Denotation each : made) {
                    Core field = fieldOf(each, access.field());
                    FormRange one = field == null ? null
                            : numbersOf(new Denotation(field, each.at()), arms);
                    if (one == null) {
                        yield derived(left);
                    }
                    hull = hull == null ? one : hull.hull(one);
                }
                yield derived(hull == null ? left : left == null ? hull : hull.meet(left));
            }
            // A quotient comes to what it is on a run that gets past a divisor of nought.
            case Core.Binary quotient when quotient.op() == BinOp.DIV
                    && quotient.right().type() == Type.INT -> {
                FormRange divided = FormRange.quotientByAWholeNumber(
                        numbersOf(new Denotation(quotient.left(), value.at()), arms),
                        numbersOf(new Denotation(quotient.right(), value.at()), arms));
                yield derived(written.type() == Type.INT ? heldToAnInt(divided) : divided);
            }
            // An operator over rationals works its number out exactly, and no type holds it.
            case Core.Binary _, Core.Neg _ -> written.type() == Type.INT
                    ? derived(heldToAnInt(whatItComesTo(value, arms)))
                    : written.type() == Type.RATIONAL ? derived(whatItComesTo(value, arms))
                    : null;
            // Any arm a run enters, read with the names it binds: one no run enters adds nothing.
            case Core.If _, Core.Match _ -> {
                List<WhereAValueComesFrom> candidates = new ArrayList<>();
                List<Choice.Arm> choices = Choice.of(written).arms();
                for (int arm = 0; arm < choices.size(); arm++) {
                    ArmsTaken entered = arms.entering(written, arm, value.at());
                    if (entered.leaveNoRun(read)) {
                        continue;
                    }
                    InputReads inside = value.at().choosing(choices.get(arm).decidedBy(), symbols,
                            newtypes);
                    WhereAValueComesFrom one = originOf(new Denotation(choices.get(arm).answers(), inside),
                            entered);
                    if (one == null) {
                        yield null;
                    }
                    candidates.add(one);
                }
                yield candidates.isEmpty() ? null : WhereAValueComesFrom.oneOf(candidates);
            }
            default -> null;
        };
    }

    /** {@code range} worked out otherwise, or null where it is not known. */
    private static WhereAValueComesFrom derived(FormRange range) {
        return range == null ? null : new WhereAValueComesFrom.Derived(range);
    }

    /** What {@code place} holds on the runs that entered {@code arms}, or null where that is not
     *  known ({@link #rangeOfAPlace}). */
    private WhereAValueComesFrom atAPlace(TermPath place, ArmsTaken arms) {
        FormRange range = rangeOfAPlace(place, arms);
        return range == null ? null : new WhereAValueComesFrom.AtAPlace(place, range);
    }

    /**
     * Where the numbers {@code name}, read in {@code at}, comes to come from where an arm bound it
     * to what a call answering an element of a container holds
     * ({@link BoundOperationFacts#answersAnElementOf}): an element of that container. Null where it
     * is no such name, or those are not known.
     */
    private WhereAValueComesFrom originOfAnOpenedElement(Core.Read name, InputReads at, ArmsTaken arms) {
        InputReads.ElementOpened opened = at.elementOpenedBy(name.binding());
        if (opened == null || !(AnOperationApplied.of(Core.withoutStanding(opened.call().value()))
                instanceof AnOperationApplied answered)) {
            return null;
        }
        var container = DefaultBoundOperationFacts.get().answersAnElementOf(answered.operation());
        Core of = container == null ? null : answered.argument(container);
        return of == null ? null : originOfAnElementOf(new Denotation(of, opened.call().at()),
                arms);
    }

    /**
     * Where the numbers a walk from a seed comes to come from, whose step answers the element it
     * is handed or what it was carried and nothing else ({@link #answersTheElementOrWhatItCarried}):
     * the seed, or an element of the container it walks, whichever the last step answered. Null
     * where {@code value} is no such walk, or the numbers of the seed or of an element are not
     * known.
     */
    private WhereAValueComesFrom originOfAWalkKept(Denotation value, ArmsTaken arms) {
        Denotation met = value.at().denotes(Core.withoutStanding(value.value()),
                read.rules().symbols(), read.rules().newtypes());
        SeededWalk walk = met == null ? null : SeededWalk.of(met.value(), closure ->
                Core.withoutStanding(closure) instanceof Core.Block block ? block : null);
        if (walk == null || !answersTheElementOrWhatItCarried(walk.step().body(),
                walk.element().binding(), walk.accumulator().binding())) {
            return null;
        }
        WhereAValueComesFrom seed = originOf(new Denotation(walk.seed(), met.at()), arms);
        WhereAValueComesFrom element = originOfAnElementOf(new Denotation(walk.container(), met.at()), arms);
        return (seed == null || element == null) ? null
                : new WhereAValueComesFrom.OneOf(List.of(seed, element));
    }

    /**
     * Where the numbers an element of {@code container} comes to come from, on the runs that
     * entered {@code arms}: each element of a list written out, or the place every element it
     * holds stands at. Null where it is neither, or holds no element written out.
     */
    private WhereAValueComesFrom originOfAnElementOf(Denotation container, ArmsTaken arms) {
        List<Denotation> written = elementsWrittenOut(container);
        List<WhereAValueComesFrom> candidates = new ArrayList<>();
        if (written != null) {
            for (Denotation each : written) {
                WhereAValueComesFrom one = originOf(each, arms);
                if (one == null) {
                    return null;
                }
                candidates.add(one);
            }
            return candidates.isEmpty() ? null : WhereAValueComesFrom.oneOf(candidates);
        }
        List<TermPath> places = switch (container.at().everyElementOf(container.value(),
                read.rules().newtypes())) {
            case ValuesHeld.At(TermPath at) -> List.of(at);
            case ValuesHeld.MayStandAt(List<TermPath> among) -> among;
            case ValuesHeld.NotAPosition _ -> List.of();
        };
        for (TermPath each : places) {
            WhereAValueComesFrom one = atAPlace(each, arms);
            if (one == null) {
                return null;
            }
            candidates.add(one);
        }
        return candidates.isEmpty() ? null : WhereAValueComesFrom.oneOf(candidates);
    }

    /**
     * Where the numbers {@code path}, a way down from a name a closure is handed an element on,
     * comes to come from, read in {@code where}: the place that way reaches inside each element
     * of the container the closure walks, as that list is written out, each held to what the
     * rules of its type leave it ({@code left}, null where they leave it open). An element a test
     * may drop is one of them, and dropping it only narrows what the closure is handed. Null where
     * the name is no element of a container, the way is no place inside an element, or an element
     * written out stands at no place.
     */
    private WhereAValueComesFrom originOfAPathOfTheElements(Core path, InputReads where,
                                                            ArmsTaken arms, FormRange left) {
        Core.Read name = theNameTheAccessesAreReadOff(path);
        return name == null ? null : originOfAWayInTheElements(path, name, where, arms, left);
    }

    /** The name a run of accesses is read off, or null where it is read off anything else. */
    private static Core.Read theNameTheAccessesAreReadOff(Core path) {
        Core root = Core.withoutStanding(path);
        while (true) {
            switch (root) {
                case Core.FieldAccess access -> root = Core.withoutStanding(access.target());
                case Core.FieldProjection projection ->
                        root = Core.withoutStanding(projection.base());
                default -> {
                    return (root instanceof Core.Read name && name.binding() != null) ? name : null;
                }
            }
        }
    }

    /** A name {@code let} binds to the one value it is given, as a helper's parameter is to what
     *  it is applied to, is followed to the name that is handed an element: the value may be that
     *  name or a way down from it, which the way read here goes through. */
    private WhereAValueComesFrom originOfAWayInTheElements(Core path, Core.Read name,
                                                           InputReads reading, ArmsTaken arms,
                                                           FormRange left) {
        DeclarationNewtypes newtypes = read.rules().newtypes();
        Map<BindingId, Core> held = new HashMap<>();
        Core.Read current = name;
        InputReads where = reading;
        Core container = where.containerOfTheElementHandedTo(current.binding());
        while (container == null) {
            List<Denotation> given = boundTo(new Denotation(current, where));
            Core.Read next = given.size() != 1 ? null
                    : theNameTheAccessesAreReadOff(given.getFirst().value());
            if (next == null || held.containsKey(current.binding())) {
                return null;
            }
            held.put(current.binding(), given.getFirst().value());
            current = next;
            where = given.getFirst().at();
            container = where.containerOfTheElementHandedTo(current.binding());
        }
        ElementProjection way = ElementProjection.read(path, current.binding(), held, newtypes);
        List<TermPath> places = way == null ? null
                : placesOfTheElementsWrittenOut(new Denotation(container, where));
        if (places == null) {
            return null;
        }
        List<WhereAValueComesFrom> candidates = new ArrayList<>();
        for (TermPath at : places) {
            TermPath place = way.from(at);
            FormRange one = rangeOfAPlace(place, arms);
            if (one == null) {
                return null;
            }
            candidates.add(new WhereAValueComesFrom.AtAPlace(place,
                    left == null ? one : one.meet(left)));
        }
        return WhereAValueComesFrom.oneOf(candidates);
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
                && whereThePartsAndNamesMayEnd(value, question).endsNone();
    }

    /** Whether what {@code value} is made of, each part on the runs that work it out, and what
     *  each name in it was given, where it was given, end no run; where not, where the first of
     *  them asked may end one. */
    private WhereItMayEnd whereThePartsAndNamesMayEnd(Denotation value, Question question) {
        Core written = Core.withoutStanding(value.value());
        for (Part part : partsOf(written)) {
            Question asked = part.arm() >= 0
                    ? question.enteringArm(written, part.arm(), value.at())
                    : Evaluated.runsWhenever(written, part.expression()) ? question
                    : question.notOnEveryRun();
            WhereItMayEnd there = whereItMayEnd(new Denotation(part.expression(), value.at()),
                    asked);
            if (!there.endsNone()) {
                return there;
            }
        }
        for (Denotation bound : boundTo(value)) {
            WhereItMayEnd there = whereItMayEnd(bound, question.whereItWasBound(bound));
            if (!there.endsNone()) {
                return there;
            }
        }
        return WhereItMayEnd.NOWHERE;
    }

    /** What the name {@code value} is was given, where it was given; none where it is no name
     *  given a value, a position of the input or what an application was handed. */
    List<Denotation> boundTo(Denotation value) {
        return value.at().boundTo(value.value(), read.rules().symbols(), read.rules().newtypes());
    }

    /**
     * A part of what a run works out to reach a value, and which arm of the value it is, as
     * {@link Choice} numbers them; {@code arm} is below nought where it is no arm.
     */
    record Part(Core expression, int arm) {}

    /**
     * The parts of {@code written} whose ending a run is the ending of a run of it: what
     * {@link Evaluated#inOrder} says is evaluated, and every branch and arm, which are not
     * evaluated by reaching the node but one of which is, so that all of them are asked. Each
     * arm comes with its number.
     *
     * <p>A function value is made and not run where it is written, so its body is not a part. The
     * construction an {@code if} tests for is a part by its fields alone: a refusal of its
     * invariant is the branch the {@code if} takes and ends nothing.
     */
    static List<Part> partsOf(Core written) {
        List<Part> parts = new ArrayList<>();
        Core fork = Core.withoutStanding(written);
        // Of an attempt, what the construction is built of: the building is the attempt's
        // deciding, and no step of it ({@link Evaluated#inOrder}).
        for (Evaluated.Step step : Evaluated.inOrder(written)) {
            parts.add(new Part(step.expression(), -1));
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
