package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.PositionsAStatementReads.ReadSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.partition.Pullback.AfterTheFirst;
import souther.compiler.partition.Pullback.Answers;
import souther.compiler.partition.Pullback.Operated;
import souther.compiler.partition.Pullback.OperatorsAnswer;
import souther.compiler.partition.Pullback.StopObligation;
import souther.compiler.partition.Pullback.WhatTheStepsNamesHold;
import souther.compiler.partition.Pullback.WorkedOutWhere;
import souther.compiler.partition.ReadingState.Restore;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The operators a reading was told of, in the order it was told, each node once for each
 * application of the closures it is written in, and what they leave unsaid and owe.
 *
 * <p>Told apart by which node each is and not by the form it came to. An {@code Int} sum and a
 * {@code Decimal} sum over the same numbers come to one form and answer in different places,
 * and the form alone would keep whichever came first. A node in the body of a closure is one
 * operator on each application, worked out over what that application is handed, so the node
 * alone would keep only the first.
 *
 * <p>Everything it holds is changed through its own methods, and every change moves a count, so
 * what it has been told ({@link #mark}) is the same only while it has been told nothing more. The
 * application being read and what the names of a walk's step hold are set for an extent and put
 * back, and are in the mark as the very values they are.
 */
final class Operators implements ReadingState.Marked {

    private final List<Operated> told = new ArrayList<>();
    /** The nodes told of wherever a run works them out: on every application of the closures
     *  around them, where there are any. */
    private final Set<Core> nodes = Collections.newSetFromMap(new IdentityHashMap<>());
    /** For a node inside a closure, the applications it was told of on. */
    private final Map<Core, Set<InputReads.Applications.Made>> toldOn = new IdentityHashMap<>();
    /** The application being read, or null outside every closure. */
    private InputReads.Applications.Made application;
    /** The closures no run applies ({@link InputReads.Applications.NoneMade}), whose bodies
     *  stop no run. */
    private final Set<Core> neverApplied = Collections.newSetFromMap(new IdentityHashMap<>());
    /** What the names of the step of a walk around hold, where the walk of what may end a run
     *  stands now ({@link WhatTheStepsNamesHold}). */
    private WhatTheStepsNamesHold stepsNames = WhatTheStepsNamesHold.NOTHING;
    private final List<Set<TermPath>> unsaidGroups = new ArrayList<>();
    /** For each of {@link #unsaidGroups}, where its operator is worked out. */
    private final List<WorkedOutWhere> unsaidGroupsWhere = new ArrayList<>();
    private Set<TermPath> unsaidAt = new LinkedHashSet<>();
    private boolean unsaidElsewhere;
    private final List<StopObligation> obligations = new ArrayList<>();
    private final List<AfterTheFirst> afterTheFirst = new ArrayList<>();
    private final Map<Core, InputReads> readsAt = new IdentityHashMap<>();
    private Core within;
    private Core leftOut;
    /** Where the comparison left out is worked out, as the closures it stands inside say, or
     *  null while the walk has not got to it. */
    private WorkedOutWhere relationStands;
    /** What a run may stop on, told over a value read at one reading and under one closure's
     *  names, since the group began: telling it again says nothing more. */
    private final Set<Visit> visited = new HashSet<>();
    /** How many times what this holds has changed. */
    private long changes;

    Operators() {
        unsaidGroups.add(unsaidAt);
        unsaidGroupsWhere.add(WorkedOutWhere.ALWAYS);
    }

    /** What these operators have been told, compared by the very operators, the count of changes
     *  and the very values set for the extent being read. */
    private record Told(Operators by, long changes, WhatTheStepsNamesHold stepsNames,
                        InputReads.Applications.Made application) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Told that && that.by == by && that.changes == changes
                    && that.stepsNames == stepsNames && that.application == application;
        }

        @Override
        public int hashCode() {
            return (System.identityHashCode(by) * 31 + Long.hashCode(changes)) * 31
                    + System.identityHashCode(stepsNames);
        }
    }

    /** What has been told so far, which is the same only while nothing more has. */
    @Override
    public Object mark() {
        return new Told(this, changes, stepsNames, application);
    }

    private void changed() {
        changes++;
    }

    /**
     * The operators of the applications of a step after the first, as this has told of them:
     * the same operators told and the same closures applied to nothing, read in the same tree,
     * with nothing yet left unsaid or owed. What it is told after is its own.
     */
    Operators ofTheApplicationsAfterTheFirst() {
        Operators out = new Operators();
        out.told.addAll(told);
        out.nodes.addAll(nodes);
        toldOn.forEach((node, on) -> {
            Set<InputReads.Applications.Made> copy =
                    Collections.newSetFromMap(new IdentityHashMap<>());
            copy.addAll(on);
            out.toldOn.put(node, copy);
        });
        out.application = application;
        out.neverApplied.addAll(neverApplied);
        out.stepsNames = stepsNames;
        out.within = within;
        out.leftOut = leftOut;
        return out;
    }

    /** What is left unsaid and owed here, with nothing told of where an operator answers. */
    OperatorsAnswer leftUnsaid() {
        return answer(Optional.empty(), List.of(), Optional.empty());
    }

    /** What is left unsaid and owed here, with where the operators said answer {@code answers},
     *  what they ask of constructions {@code asked}, and those that answer at the ends of what
     *  their type holds {@code atTheEnds}. */
    OperatorsAnswer answer(Optional<Proposition> answers, List<ConstructionAsk> asked,
                           Optional<Proposition> atTheEnds) {
        return new OperatorsAnswer(answers, unsaidGroups, unsaidGroupsWhere, unsaidElsewhere,
                obligations, afterTheFirst, relationStandsWhere(), asked, atTheEnds);
    }

    /** The operators told, in the order they were told. */
    List<Operated> told() {
        return Collections.unmodifiableList(told);
    }

    /** How many operators have been told. */
    int toldSoFar() {
        return told.size();
    }

    void tell(Core operation, Answers where) {
        boolean first = application == null ? nodes.add(operation)
                : toldOn.computeIfAbsent(operation,
                        _ -> Collections.newSetFromMap(new IdentityHashMap<>()))
                        .add(application);
        if (first) {
            told.add(new Operated(operation, where));
            changed();
        }
    }

    /** Whether {@code node} was told of wherever a run works it out. */
    boolean toldWhereverItRuns(Core node) {
        return nodes.contains(node);
    }

    /**
     * That {@code each}, the applications of one closure, were read, telling what is in
     * {@link #told} from {@code from} on: a node of its body told of on every one of them is
     * told of on the application around them, or wherever a run works it out where there is
     * none.
     *
     * <p>Only the nodes told of while they were read are asked. Every node told of on one of
     * them was told there first on that application, and so is among those.
     */
    void toldOnEach(List<InputReads.Applications.Made> each, int from) {
        Set<InputReads.Applications.Made> all = Collections.newSetFromMap(
                new IdentityHashMap<>());
        all.addAll(each);
        Set<Core> asked = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Operated one : told.subList(from, told.size())) {
            Set<InputReads.Applications.Made> on = toldOn.get(one.operation());
            if (asked.add(one.operation()) && on != null && on.containsAll(all)
                    && (application == null ? nodes.add(one.operation())
                            : on.add(application))) {
                changed();
            }
        }
    }

    /** The application being read, or null outside every closure. */
    InputReads.Applications.Made application() {
        return application;
    }

    /** Reads on {@code one}, an application of a closure, until what is returned is closed. */
    Restore onTheApplication(InputReads.Applications.Made one) {
        InputReads.Applications.Made before = application;
        application = one;
        return () -> application = before;
    }

    /** What the names of the step of a walk around hold, where the walk stands now. */
    WhatTheStepsNamesHold stepsNames() {
        return stepsNames;
    }

    /** The names of the step of a walk around hold {@code held} until what is returned is
     *  closed. */
    Restore withTheStepsNames(WhatTheStepsNamesHold held) {
        WhatTheStepsNamesHold before = stepsNames;
        stepsNames = held;
        return () -> stepsNames = before;
    }

    /** That {@code block}, a closure, is applied on no run. */
    void appliedOnNoRun(Core block) {
        if (neverApplied.add(block)) {
            changed();
        }
    }

    /** Whether {@code block} is a closure applied on no run. */
    boolean isAppliedOnNoRun(Core block) {
        return neverApplied.contains(block);
    }

    /** That what is read is {@code body}, where the operators that owe a proof are owed. */
    void readWithin(Core body) {
        within = body;
        changed();
    }

    /** That the comparison {@code leftOut} is left out of what is read. */
    void leaveOut(Core leftOut) {
        this.leftOut = leftOut;
        changed();
    }

    /** The comparison left out of what is read, or null where none is. */
    Core leftOut() {
        return leftOut;
    }

    /** That names at {@code node} are read in {@code reads}, where they were not read so
     *  before. */
    void readAt(Core node, InputReads reads) {
        if (readsAt.putIfAbsent(node, reads) == null) {
            changed();
        }
    }

    /** The walk got to the comparison left out, worked out where {@code inside} says. */
    void relationIsInside(WorkedOutWhere inside) {
        relationStands = relationStands == null ? inside : relationStands.and(inside);
        changed();
    }

    /**
     * Where a run works out the comparison: anywhere where none is left out of the part read;
     * where its closures say where the walk got to it; and not said where one is left out and
     * the walk did not get to it.
     */
    WorkedOutWhere relationStandsWhere() {
        if (leftOut == null) {
            return WorkedOutWhere.ALWAYS;
        }
        return relationStands == null ? WorkedOutWhere.ALWAYS.notSaid() : relationStands;
    }

    /** What the next operator not said of may stop a run on is one group of places: it ties
     *  them to one another, which what another operator stops a run on does not. */
    void beginGroup() {
        beginGroup(WorkedOutWhere.ALWAYS);
    }

    /** The same, of an operator a run works out where {@code where} says. */
    void beginGroup(WorkedOutWhere where) {
        unsaidAt = new LinkedHashSet<>();
        unsaidGroups.add(unsaidAt);
        unsaidGroupsWhere.add(where);
        visited.clear();
        changed();
    }

    /** Whether the group begun last names no place. */
    boolean noPlaceUnsaidInTheGroup() {
        return unsaidAt.isEmpty();
    }

    /** Whether an operator not said may stop a run on something that is no number of a place. */
    boolean unsaidElsewhere() {
        return unsaidElsewhere;
    }

    /**
     * That the operator {@code operation}, whose group began last, owes a proof that it completes
     * ({@code completion}) rather than leaving unsaid what it may stop a run on: what the group
     * named is owed, and the group is emptied and told again from {@code elsewhereBefore}.
     */
    void owe(Core operation, boolean elsewhereBefore, GetsPast completion,
             WorkedOutWhere where) {
        obligations.add(new StopObligation(operation, unsaidAt,
                unsaidElsewhere != elsewhereBefore, completion, within,
                Collections.unmodifiableMap(readsAt), where));
        unsaidAt.clear();
        unsaidElsewhere = elsewhereBefore;
        visited.clear();
        changed();
    }

    /** Whether operators that owe a proof are owed here, which is where a body is read whole. */
    boolean owesWithin() {
        return within != null;
    }

    /** That {@code after}, what the applications of a step after the first leave, is owed of a
     *  run walking more than one element. */
    void afterTheFirst(AfterTheFirst after) {
        afterTheFirst.add(after);
        changed();
    }

    private record Visit(Core node, InputReads reads, Pullback.Bound bound) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Visit that && node == that.node && bound == that.bound
                    && reads.equals(that.reads);
        }

        @Override
        public int hashCode() {
            return (System.identityHashCode(node) * 31 + reads.hashCode()) * 31
                    + System.identityHashCode(bound);
        }
    }

    /**
     * Whether what a run may stop on over {@code operand} has not been told yet in this group.
     * A value several names stand for, or several operands of an operator are made of, is
     * told once and not once for every way down to it.
     */
    boolean firstOverWhereItStands(Core operand, InputReads reads, Pullback.Bound bound) {
        if (!visited.add(new Visit(Core.withoutStanding(operand), reads, bound))) {
            return false;
        }
        changed();
        return true;
    }

    /** Every place any operator not said of may stop a run on. */
    Set<TermPath> everyPlaceUnsaid() {
        Set<TermPath> out = new LinkedHashSet<>();
        unsaidGroups.forEach(out::addAll);
        return out;
    }

    /** That the operator whose group began last may stop a run on what is at {@code path}. */
    void unsaidAt(TermPath path) {
        if (unsaidAt.add(path)) {
            changed();
        }
    }

    /** The same, of each of {@code paths}. */
    void unsaidAtEach(Collection<TermPath> paths) {
        if (unsaidAt.addAll(paths)) {
            changed();
        }
    }

    /** An operator that may stop a run where nothing is said, over {@code reads}: the places
     *  each of them is read off are the ones it may stop on, a remainder's those of its
     *  dividend ({@link PositionsAStatementReads#ofANumber}), and a quantity read off
     *  anything else leaves it stopping on no place this can name. */
    void leaveUnsaid(Collection<? extends Quantity> reads, Pullback.Bound bound) {
        leaveUnsaid(reads, bound, null);
    }

    /** The same, where a name another name was given is the name it was given, read in
     *  {@code at}. */
    void leaveUnsaid(Collection<? extends Quantity> reads, Pullback.Bound bound, InputReads at) {
        for (Quantity each : reads) {
            Optional<Set<ReadSubject>> read = PositionsAStatementReads.ofANumber(each);
            if (read.isEmpty()) {
                leaveUnsaidOverUnreadOperands();
                continue;
            }
            for (ReadSubject subject : read.get()) {
                switch (subject) {
                    case ReadSubject.At(TermPath path) -> unsaidAt(path);
                    case ReadSubject.Bound(var named) ->
                            leaveUnsaidOver(at != null && bound != null
                                    && !bound.names().contains(named.binding())
                                    ? at.namedBy(named.binding()) : named.binding(), bound);
                }
            }
        }
    }

    /** The same, over a name: the places of what a closure around binds it to where it is a
     *  name of one, and no place this can name where it is not. */
    void leaveUnsaidOver(BindingId name, Pullback.Bound bound) {
        if (bound != null && bound.standFor() != null && bound.names().contains(name)) {
            unsaidAtEach(bound.standFor());
        } else {
            leaveUnsaidOverUnreadOperands();
        }
    }

    /** An operator that may stop a run where nothing is said, over operands no form says. */
    void leaveUnsaidOverUnreadOperands() {
        if (!unsaidElsewhere) {
            unsaidElsewhere = true;
            changed();
        }
    }
}
