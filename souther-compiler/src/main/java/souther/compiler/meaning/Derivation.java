package souther.compiler.meaning;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.TheSignOfAnOrder;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawArguments;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * How what a condition states was arrived at: the rule each step applied and what it was applied to.
 *
 * <p>One rule, one kind. A step holds the derivations of its premises and nothing that says what it
 * concludes, because the conclusion is the rule's to compute: an {@code if} states what its arms do
 * under its condition and its denial, whatever its caller expected. So a proposition reaches a reader
 * only through a rule in this set, and a step no rule takes cannot be written.
 *
 * <p>A leaf is a ground of a kind — a value written out, a position of the input, a comparison read
 * as a relation over the input's quantities, a part that was not read — and builds its part from what
 * that ground says. Nothing here takes a proposition and hands it back as derived.
 *
 * <p>What is concluded is the proposition and nothing beside it. Two derivations of one proposition
 * conclude the same thing and are still two derivations, so the proposition is what a reader that
 * counts what a condition states compares, and the derivation is what one that explains it reads.
 */
public sealed interface Derivation {

    /**
     * What this concludes, with every part it could not read named as {@code numbering} says.
     *
     * <p>Premises are concluded in the order they are held, which is the order a reading meets
     * them, so the parts nothing read are numbered as they were met.
     */
    Proposition conclusion(Conclusion numbering);

    /** What this concludes, read at {@code where}. */
    default Proposition concludes(Optional<ModelOccurrence> where) {
        return new Conclusion(where).of(this);
    }

    /**
     * The steps this one states what one of them states, each where it is taken — the arms of a
     * choice, the value a name stands for, what a body or each application states — or null where
     * this states something of its own.
     *
     * <p>What a law's comparison is read as is asked through these to the comparisons under them:
     * an argument chosen by cases is compared in each case, and every one of those is a comparison
     * the law states. A step that answers null here is taken as stating its own, so one added later
     * that does not say what it answers with is no reading of a law's comparison.
     */
    default List<Derivation> oneOf() {
        return null;
    }

    // The steps a construct of the language takes by its own semantics.

    /** A value read through the name or binding that stands for it: what the value states. */
    record ThroughABinding(Derivation value) implements Derivation {

        public ThroughABinding {
            Objects.requireNonNull(value, "a binding stands for a value");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(value);
        }

        @Override
        public List<Derivation> oneOf() {
            return List.of(value);
        }
    }

    /**
     * What a behavior a call names answers, read off its body where the call stands: the body's
     * parameters stand for what the call handed, so what the body states of them is what it states
     * of the call's arguments.
     */
    record ABehaviorsBody(ValueName.Behavior behavior, Derivation inItsBody) implements Derivation {

        public ABehaviorsBody {
            Objects.requireNonNull(behavior, "a call names a behavior");
            Objects.requireNonNull(inItsBody, "whose body states something");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(inItsBody);
        }

        @Override
        public List<Derivation> oneOf() {
            return List.of(inItsBody);
        }
    }

    /**
     * What is read where a name stands for one of the values a container was written with, read once
     * for each of them: on an application the name is that value, so what is stated is what is
     * stated on the application handing it each ({@link Proposition.OnAnApplication}).
     */
    record OnEachValueWrittenOut(List<Derivation> each) implements Derivation {

        public OnEachValueWrittenOut {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("a name stands for some values");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> stated = new ArrayList<>();
            each.forEach(one -> stated.add(numbering.of(one)));
            return Proposition.onAnApplication(stated);
        }

        @Override
        public List<Derivation> oneOf() {
            return each;
        }
    }

    /** An {@code if}: its arm under its condition, and its other arm under the denial of it. */
    record IfThenElse(Derivation condition, Derivation then, Derivation otherwise)
            implements Derivation {

        public IfThenElse {
            Objects.requireNonNull(condition, "an if is decided by a condition");
            Objects.requireNonNull(then, "an if has an arm for its condition");
            Objects.requireNonNull(otherwise, "an if has an arm for its denial");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition cond = numbering.of(condition);
            Proposition yes = numbering.of(then);
            Proposition no = numbering.of(otherwise);
            return Proposition.any(List.of(Proposition.all(List.of(cond, yes)),
                    Proposition.all(List.of(cond.denied(), no))));
        }

        @Override
        public List<Derivation> oneOf() {
            return List.of(then, otherwise);
        }
    }

    /**
     * A {@code match}: an arm is taken where it selects the value and no arm before it does, and
     * what is stated is what the arm taken states.
     */
    record MatchArms(List<Arm> arms) implements Derivation {

        public MatchArms {
            if (arms == null || arms.isEmpty()) {
                throw new IllegalArgumentException("a match has an arm");
            }
            arms = List.copyOf(arms);
        }

        /** One arm: whether it selects the value, and what it states once taken. */
        public record Arm(Derivation selects, Derivation states) {

            public Arm {
                Objects.requireNonNull(selects, "an arm selects some values");
                Objects.requireNonNull(states, "an arm states something");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> taken = new ArrayList<>();
            List<Proposition> before = new ArrayList<>();
            for (Arm arm : arms) {
                Proposition selects = numbering.of(arm.selects());
                List<Proposition> arrives = new ArrayList<>(before.stream()
                        .map(Proposition::denied).toList());
                arrives.add(selects);
                arrives.add(numbering.of(arm.states()));
                taken.add(Proposition.all(arrives));
                before.add(selects);
            }
            return Proposition.any(taken);
        }

        @Override
        public List<Derivation> oneOf() {
            return statesOf(arms);
        }

        /** What each of {@code arms} states once taken. */
        static List<Derivation> statesOf(List<Arm> arms) {
            List<Derivation> out = new ArrayList<>(arms.size());
            arms.forEach(arm -> out.add(arm.states()));
            return out;
        }
    }

    /**
     * An arm of a {@code match} entered, or a case of the definition the library writes an
     * operation in: it selects the value, and no arm written before it does.
     *
     * @param before whether each arm written before it selects the value, in the order they are
     *               written
     */
    record AnArmTaken(List<Derivation> before, Derivation selects) implements Derivation {

        public AnArmTaken {
            before = List.copyOf(before);
            Objects.requireNonNull(selects, "an arm selects some values");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> arrives = new ArrayList<>();
            for (Derivation each : before) {
                arrives.add(numbering.of(each).denied());
            }
            arrives.add(numbering.of(selects));
            return Proposition.all(arrives);
        }
    }

    /**
     * An attempt that built its value: every clause of the invariant it checks held where it was
     * given what the attempt hands it.
     *
     * @param clauses whether each clause holds, in the order a construction checks them
     */
    record ItWasBuilt(List<Derivation> clauses) implements Derivation {

        public ItWasBuilt {
            clauses = List.copyOf(clauses);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return Proposition.all(clauses.stream().map(numbering::of).toList());
        }
    }

    /**
     * An attempt that departed by one of its departures: the first clause of the invariant not to
     * hold is one the departure answers. A clause is checked only where every clause before it held,
     * so the departure is taken where, for some clause it answers, every clause before that one holds
     * and that one does not.
     *
     * @param clauses  whether each clause holds, in the order a construction checks them
     * @param answers  whether the departure answers each clause, beside it in {@code clauses}
     */
    record ItDeparted(List<Derivation> clauses, List<Boolean> answers) implements Derivation {

        public ItDeparted {
            clauses = List.copyOf(clauses);
            answers = List.copyOf(answers);
            if (clauses.size() != answers.size()) {
                throw new IllegalArgumentException("a departure answers each clause or does not");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> holds = clauses.stream().map(numbering::of).toList();
            List<Proposition> firstFailing = new ArrayList<>();
            for (int i = 0; i < holds.size(); i++) {
                if (answers.get(i)) {
                    List<Proposition> taken = new ArrayList<>(holds.subList(0, i));
                    taken.add(holds.get(i).denied());
                    firstFailing.add(Proposition.all(taken));
                }
            }
            return Proposition.any(firstFailing);
        }
    }

    /**
     * Arms a run takes one of: an arm holds where it is reached and what it answers holds there. The
     * arms exclude each other, each written with every arm before it, so no arm is reached where
     * another is.
     */
    record OneOfItsArms(List<MatchArms.Arm> arms) implements Derivation {

        public OneOfItsArms {
            if (arms == null || arms.isEmpty()) {
                throw new IllegalArgumentException("a value chosen by arms has an arm");
            }
            arms = List.copyOf(arms);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> taken = new ArrayList<>();
            for (MatchArms.Arm arm : arms) {
                taken.add(Proposition.all(List.of(numbering.of(arm.selects()),
                        numbering.of(arm.states()))));
            }
            return Proposition.any(taken);
        }

        @Override
        public List<Derivation> oneOf() {
            return MatchArms.statesOf(arms);
        }
    }

    /**
     * A comparison of a value chosen by cases: the choice, with the comparison of what each case
     * answers in that case's place. A value is what the case taken answers, so a comparison of it
     * holds exactly where the comparison of that answer does.
     */
    record AComparisonOfAChoice(Derivation byItsCases) implements Derivation {

        public AComparisonOfAChoice {
            Objects.requireNonNull(byItsCases, "a choice is made by its cases");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(byItsCases);
        }

        @Override
        public List<Derivation> oneOf() {
            return List.of(byItsCases);
        }
    }

    /**
     * The cases the library writes {@code operation}'s definition in: a case is taken where its
     * arguments stand as it says and none before it, and what is stated is what the case taken
     * states. The library's cases cover everything the operation can be given, which is what makes
     * the choice between them the operation.
     *
     * <p>One arm for each case the library defines the operation by, in its order, so a choice
     * the definition does not make is refused where it is made.
     */
    record AnOperationsCases(ValueName.Stdlib operation, List<MatchArms.Arm> cases)
            implements Derivation {

        public AnOperationsCases {
            Objects.requireNonNull(operation, "cases are an operation's");
            if (cases == null || cases.isEmpty()) {
                throw new IllegalArgumentException("an operation defined by cases has a case");
            }
            cases = List.copyOf(cases);
            int defined = DefaultBoundOperationFacts.get().isDefinedByCases(operation).size();
            if (defined != cases.size()) {
                throw new IllegalArgumentException(operation + " is defined in " + defined
                        + " cases and is read in " + cases.size());
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new MatchArms(cases).conclusion(numbering);
        }

        @Override
        public List<Derivation> oneOf() {
            return MatchArms.statesOf(cases);
        }
    }

    /**
     * How many {@code operation} answers holds, by the cases its law says it in: a case is taken
     * where its arguments stand as it says and none before it, and what is stated is what is read
     * with the answer holding as many as that case says.
     *
     * <p>The law is the one the library settles the operation's size by, and each arm is taken
     * under a reading of its case ({@link ByALaw#readsTheLaw}) of {@code call}, one for each
     * case, in its order.
     */
    record ASizeInCases(TheCall call, List<MatchArms.Arm> cases) implements Derivation {

        public ASizeInCases {
            Objects.requireNonNull(call, "a size is of what a call of an operation answers");
            cases = List.copyOf(cases);
            if (!(settled(call.operation(), OperationLaw.Observed.SIZE)
                    instanceof OperationLaw.Size<DeclaredArgument> law)
                    || law.cases().size() != cases.size()) {
                throw new IllegalArgumentException("how many " + call.operation()
                        + " answers is read in " + cases.size() + " cases, and no law says it in"
                        + " those");
            }
            for (int i = 0; i < cases.size(); i++) {
                if (!ByALaw.readsTheLaw(law.cases().get(i).where(), cases.get(i).selects(),
                        call)) {
                    throw new IllegalArgumentException(cases.get(i).selects() + " is no reading"
                            + " of case " + (i + 1) + " of how many " + call.operation()
                            + " answers: " + law.cases().get(i).where());
                }
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new MatchArms(cases).conclusion(numbering);
        }

        @Override
        public List<Derivation> oneOf() {
            return MatchArms.statesOf(cases);
        }
    }

    /**
     * The law the library settles {@code observed} of what {@code operation} answers by, or null
     * where none settles it: a law a step of a reading names is taken from here and from nowhere
     * else.
     */
    private static OperationLaw<DeclaredArgument> settled(ValueName.Stdlib operation,
                                                          OperationLaw.Observed observed) {
        return DefaultBoundOperationFacts.get().settled(operation, observed)
                instanceof BoundOperationFacts.Settled.ByALaw(
                        OperationLaw<DeclaredArgument> law, var _) ? law : null;
    }

    /**
     * A truth held against a truth the source settles: {@code x == true} holding is {@code x}
     * holding, and {@code x == false} holding is {@code x} not holding.
     */
    record HeldAgainstAWrittenTruth(Derivation truth, boolean held) implements Derivation {

        public HeldAgainstAWrittenTruth {
            Objects.requireNonNull(truth, "a truth is held against one written out");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition stated = numbering.of(truth);
            return held ? stated : stated.denied();
        }
    }

    /** A denial: what is under it, the other way round where it denies. */
    record UnderADenial(Derivation part, boolean denies) implements Derivation {

        public UnderADenial {
            Objects.requireNonNull(part, "a denial is of something");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition under = numbering.of(part);
            return denies ? under.denied() : under;
        }
    }

    /** Two truths joined by a connective, coming out true. */
    record Joined(ConditionJoin how, Derivation left, Derivation right) implements Derivation {

        public Joined {
            Objects.requireNonNull(how, "a join is one of two");
            Objects.requireNonNull(left, "a join has a left half");
            Objects.requireNonNull(right, "a join has a right half");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> parts = List.of(numbering.of(left), numbering.of(right));
            return how == ConditionJoin.BOTH ? Proposition.all(parts) : Proposition.any(parts);
        }
    }

    /**
     * A size held against a number that parts nought from every size above it: whether the container
     * holds anything, or the denial of that where the comparison holds of an empty one.
     */
    record AnEmptinessCheck(Derivation holdsSomething, boolean emptyWhereItHolds)
            implements Derivation {

        public AnEmptinessCheck {
            Objects.requireNonNull(holdsSomething, "an emptiness check asks whether a container"
                    + " holds anything");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition some = numbering.of(holdsSomething);
            return emptyWhereItHolds ? some.denied() : some;
        }
    }

    // The steps a law the library declares licenses.

    /**
     * Where the arguments of one call of {@code operation} stand: the position of the input each
     * argument a law names stands at, for those that stand at one. An argument that stands at none
     * is an expression, and is not in the map.
     *
     * <p>What a reading of a law is held to. A law names its arguments, and a reading of it says
     * where each of them is read off; a reading that has one standing at another argument's
     * position, or at the position of an argument of some other call, says something of a call
     * that was not made.
     */
    record TheCall(ValueName.Stdlib operation, Map<DeclaredArgument, TermPath> standingAt) {

        public TheCall {
            Objects.requireNonNull(operation, "a call is of an operation");
            standingAt = Map.copyOf(standingAt);
        }
    }

    /**
     * An operation whose answer comes out on {@code aspect}'s holding side exactly where its law
     * says of the arguments, read as {@code ofTheArguments}.
     *
     * <p>The law is the one the library settles that side by, taken from the settlement and never
     * handed in. What the reading concludes is the law's to compute: each step of it holds the
     * part of the law it reads ({@link ALawPart}) and works its conclusion out from that part and
     * from what the arguments were read as — a connective joins as the law joins, a side is denied
     * where the law denies it, a comparison is the law's own form over the numbers the arguments
     * were read as. So a reading is held to be of the law part for part, at every step: a step
     * holding a part of another law, or the right part at the wrong place, is refused where it is
     * made, and no step hands in a relation, a polarity or a container of its own.
     *
     * <p>And it is held to the call. Where an argument stands is what {@code call} says, and a step
     * that reads a position for an argument — the container some element is of, the subject a side
     * is observed of, what a number is a size of — reads the one the argument stands at, or one
     * inside it where the law says an element or a key of it. How an argument that stands at no
     * position is read is the reading rules' own, and is held to nothing here.
     */
    record ByALaw(TheCall call, AnswerAspect aspect, Derivation ofTheArguments)
            implements Derivation {

        public ByALaw {
            Objects.requireNonNull(call, "a law is of a call of an operation");
            Objects.requireNonNull(aspect, "a law is about one side of what it answers");
            Objects.requireNonNull(ofTheArguments, "and comes to something of its arguments");
            if (!(settled(call.operation(), OperationLaw.Observed.of(aspect))
                    instanceof OperationLaw.Observation<DeclaredArgument> law)) {
                throw new IllegalArgumentException(call.operation() + " settles no side "
                        + aspect + " of its answer by a law");
            }
            if (!readsTheLaw(law.equivalentTo(), ofTheArguments, call)) {
                throw new IllegalArgumentException(ofTheArguments + " is no reading of what the"
                        + " law of " + call.operation() + " states of " + call.standingAt()
                        + ": " + law.equivalentTo());
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(ofTheArguments);
        }

        /**
         * Whether {@code read} is a reading of {@code law}, part for part: a step holding the very
         * part at each place, with the steps under it readings of that part's own parts — or a
         * place the reading stopped at, which is said rather than read. Each position a step reads
         * for an argument is the one {@code call} has that argument at.
         */
        static boolean readsTheLaw(LawProposition<DeclaredArgument> law, Derivation read,
                                   TheCall call) {
            return new Standing(call, Set.of()).reads(law, read);
        }

        /**
         * A call and the containers a reading is inside the written-out values of: the elements of
         * those are values, and stand at no position of the input.
         */
        private record Standing(TheCall call, Set<DeclaredArgument> writtenOut) {

            boolean reads(LawProposition<DeclaredArgument> law, Derivation read) {
                if (read instanceof Stopped) {
                    return true;
                }
                return switch (law) {
                    case LawProposition.Always<DeclaredArgument> _ ->
                            read instanceof ALawSettles(var part) && part.equals(law);
                    case LawProposition.All<DeclaredArgument>(var parts) ->
                            joins(law, parts, read);
                    case LawProposition.Any<DeclaredArgument>(var parts) ->
                            joins(law, parts, read);
                    case LawProposition.Observed<DeclaredArgument> observed ->
                            read instanceof OnTheSideALawNames(var part, Derivation seen)
                                    && part.equals(law) && observes(observed.of(), seen);
                    case LawProposition.Same<DeclaredArgument> same ->
                            read instanceof TheSameValue(var part, var one, var other)
                                    && part.equals(law) && stands(same.one(), one)
                                    && stands(same.other(), other);
                    case LawProposition.SomeElement<DeclaredArgument> some ->
                            read instanceof ALawQuantifies(var part, Derivation meeting)
                                    && part.equals(law) && meets(some, meeting);
                    case LawProposition.Compared<DeclaredArgument> compared ->
                            compares(compared, read);
                };
            }

            /** Whether {@code read} joins a reading of each of {@code parts}, in order, as
             *  {@code law} joins them. */
            private boolean joins(LawProposition<DeclaredArgument> law,
                                  List<LawProposition<DeclaredArgument>> parts, Derivation read) {
                if (!(read instanceof ALawJoins(var part, List<Derivation> joined))
                        || !part.equals(law) || joined.size() != parts.size()) {
                    return false;
                }
                for (int i = 0; i < parts.size(); i++) {
                    if (!reads(parts.get(i), joined.get(i))) {
                        return false;
                    }
                }
                return true;
            }

            /**
             * Whether {@code read} is some element meeting a reading of what {@code some} says it
             * meets: of the element standing at the container's element, or of each value the
             * container was written with.
             */
            private boolean meets(LawProposition.SomeElement<DeclaredArgument> some,
                                  Derivation read) {
                return switch (read) {
                    case Stopped _ -> true;
                    case SomeElementMeeting(TermPath container, Derivation ofTheElement,
                                            boolean holds, var _) ->
                            holds && standsAt(some.container(), container)
                                    && reads(some.ofTheElement(), ofTheElement);
                    case OverElementsWrittenOut(List<Derivation> ofEach, boolean holds) -> {
                        Set<DeclaredArgument> inside = new HashSet<>(writtenOut);
                        inside.add(some.container());
                        Standing within = new Standing(call, inside);
                        yield holds && ofEach.stream()
                                .allMatch(each -> within.reads(some.ofTheElement(), each));
                    }
                    default -> false;
                };
            }

            /**
             * Whether {@code read} is {@code law}'s comparison, read over the arguments: the law's
             * own comparison, with each of its numbers read of the argument it names, or a step
             * that states what one of the steps under it states — an argument chosen by cases
             * compared in each, one answered through a body — every one of which is the law's
             * comparison in its turn.
             */
            private boolean compares(LawProposition.Compared<DeclaredArgument> law,
                                     Derivation read) {
                if (read instanceof Stopped) {
                    return true;
                }
                if (read instanceof ALawComparison(var part, var numbers, var _)) {
                    return part.equals(law) && law.form().coefs().keySet().stream()
                            .allMatch(number -> numberStands(number, numbers.get(number)));
                }
                List<Derivation> oneOf = read.oneOf();
                return oneOf != null && !oneOf.isEmpty()
                        && oneOf.stream().allMatch(each -> compares(law, each));
            }

            /** Whether the container {@code argument} is, read at {@code container}, stands
             *  there: at the position the call has it at, where it has it at one. */
            private boolean standsAt(DeclaredArgument argument, TermPath container) {
                TermPath at = call.standingAt().get(argument);
                return at == null || at.equals(container);
            }

            /**
             * The positions the arguments {@code named} stand at, or null where a reading of them
             * is held to none: one stands at no position, or is read as the values it was
             * written with.
             */
            private List<TermPath> rootsOf(Set<DeclaredArgument> named) {
                List<TermPath> roots = new ArrayList<>();
                for (DeclaredArgument argument : named) {
                    TermPath at = call.standingAt().get(argument);
                    if (at == null || writtenOut.contains(argument)) {
                        return null;
                    }
                    roots.add(at);
                }
                return roots.isEmpty() ? null : roots;
            }

            /** Whether what {@code seen} concludes of {@code subject} is of the position the
             *  call has it at. What a closure answers is read in the closure's body, which has no
             *  position of the call's. */
            private boolean observes(LawSubject<DeclaredArgument> subject, Derivation seen) {
                if (subject instanceof LawSubject.WhatTheClosureAnswers<DeclaredArgument>) {
                    return true;
                }
                List<TermPath> roots = rootsOf(LawArguments.named(subject));
                return roots == null || seen.concludes(Optional.empty()).staysWithin(roots);
            }

            /** Whether {@code read}, the subject {@code subject} was read as, stands at the
             *  position the call has it at. */
            private boolean stands(LawSubject<DeclaredArgument> subject, DecisionSubject read) {
                List<TermPath> roots = rootsOf(LawArguments.named(subject));
                return roots == null || (read instanceof DecisionSubject.AnInput(TermPath at)
                        && at.isAtOrUnderAny(roots));
            }

            /** Whether {@code form}, what {@code number} was read as, is of the positions the
             *  call has the arguments the number names at. */
            private boolean numberStands(LawNumber<DeclaredArgument> number,
                                         LinearForm<Quantity> form) {
                List<TermPath> roots = rootsOf(LawArguments.named(number));
                return roots == null || form.coefs().keySet().stream()
                        .allMatch(quantity -> quantity.staysWithin(roots));
            }
        }
    }

    /** A step that reads one part of a law, which it holds. */
    sealed interface ALawPart extends Derivation
            permits ALawSettles, ALawJoins, OnTheSideALawNames, TheSameValue, ALawQuantifies,
                    ALawComparison {

        /** The part of the law this reads. */
        LawProposition<?> part();
    }

    /** A part of a law that says the same thing whatever the arguments are. */
    record ALawSettles(LawProposition.Always<?> part) implements ALawPart {

        public ALawSettles {
            Objects.requireNonNull(part, "a step reads a part of a law");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(part.holds());
        }
    }

    /** A part of a law that states every one of its parts, or at least one, read as {@code parts}
     *  in its order. */
    record ALawJoins(LawProposition<?> part, List<Derivation> parts) implements ALawPart {

        public ALawJoins {
            parts = List.copyOf(parts);
            int joined = switch (part) {
                case LawProposition.All<?>(var each) -> each.size();
                case LawProposition.Any<?>(var each) -> each.size();
                case null, default -> throw new IllegalArgumentException(
                        "a law joins statements with a connective: " + part);
            };
            if (joined != parts.size()) {
                throw new IllegalArgumentException("a law joining " + joined
                        + " statements is read as " + parts.size());
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> each = new ArrayList<>(parts.size());
            parts.forEach(one -> each.add(numbering.of(one)));
            return part instanceof LawProposition.All<?> ? Proposition.all(each)
                    : Proposition.any(each);
        }
    }

    /**
     * A part of a law that states a value comes out on a side, with {@code observed} what that
     * value coming out on the side's holding side was read as; the law's part says which of the
     * two sides.
     */
    record OnTheSideALawNames(LawProposition.Observed<?> part, Derivation observed)
            implements ALawPart {

        public OnTheSideALawNames {
            Objects.requireNonNull(part, "a step reads a part of a law");
            Objects.requireNonNull(observed, "a side is of something read");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition read = numbering.of(observed);
            return part.side().holds() ? read : read.denied();
        }
    }

    /** A part of a law that states two values are one, or not, with the two read as
     *  {@code one} and {@code other}. */
    record TheSameValue(LawProposition.Same<?> part, DecisionSubject one, DecisionSubject other)
            implements ALawPart {

        public TheSameValue {
            Objects.requireNonNull(part, "a step reads a part of a law");
            Objects.requireNonNull(one, "a sameness is of two subjects");
            Objects.requireNonNull(other, "a sameness is of two subjects");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.SameValue(one, other, part.holds());
        }
    }

    /**
     * A part of a law that states some element of a container meets a statement, or none does,
     * with {@code meeting} some element meeting it read: over the element standing at a position,
     * or over each value written out.
     */
    record ALawQuantifies(LawProposition.SomeElement<?> part, Derivation meeting)
            implements ALawPart {

        public ALawQuantifies {
            Objects.requireNonNull(part, "a step reads a part of a law");
            Objects.requireNonNull(meeting, "some element meeting a statement is read");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition some = numbering.of(meeting);
            return part.holds() ? some : some.denied();
        }
    }

    /**
     * A part of a law that compares a form over numbers of the arguments with nought, with each of
     * those numbers read as {@code numbers} says: the law's own form over what they were read as,
     * standing as the law's part says.
     *
     * <p>The form is worked out here and not handed in, so the relation a reading concludes is
     * the law's at every place — a reading can say only what each number of the law was read as,
     * and says it for every number the part names and no other.
     *
     * @param counts how each count the form names was read: what the elements counted meet, as
     *               {@link AComparisonRead} holds it, and held to the form there
     */
    record ALawComparison(LawProposition.Compared<?> part,
                          Map<LawNumber<?>, LinearForm<Quantity>> numbers,
                          List<AComparisonRead.Counted> counts)
            implements ALawPart {

        /**
         * {@code part} with its numbers read as {@code numbers}, holding of {@code counting} the
         * counts the form still names: a count on both sides comes to nought and names none.
         */
        public static ALawComparison of(LawProposition.Compared<?> part,
                                        Map<LawNumber<?>, LinearForm<Quantity>> numbers,
                                        Map<Quantity.HowManyMeet, AComparisonRead.Counted>
                                                counting) {
            Map<Quantity, ExactRatio> named = formOf(part.form(), numbers)
                    instanceof ExactAnswer.Held<LinearForm<Quantity>>(var form)
                    ? Relation.OneWay.of(form, part.states()).form().coefs() : Map.of();
            List<AComparisonRead.Counted> counts = new ArrayList<>();
            counting.forEach((count, how) -> {
                if (named.containsKey(count)) {
                    counts.add(how);
                }
            });
            return new ALawComparison(part, numbers, counts);
        }

        public ALawComparison {
            Objects.requireNonNull(part, "a step reads a part of a law");
            numbers = Map.copyOf(numbers);
            counts = List.copyOf(counts);
            if (!numbers.keySet().equals(part.form().coefs().keySet())) {
                throw new IllegalArgumentException("a comparison over " + part.form().coefs()
                        .keySet() + " is read with " + numbers.keySet());
            }
            if (!(formOf(part.form(), numbers)
                    instanceof ExactAnswer.Held<LinearForm<Quantity>>)) {
                throw new IllegalArgumentException("a comparison over numbers it cannot hold is"
                        + " stopped at, and not read: " + part);
            }
        }

        /**
         * {@code form}, a form a law writes over numbers of the arguments, over {@code numbers},
         * what each of those was read as at a call: each weighed as the law weighs it — or which
         * way that is not held. The one place a law's number is put together from its arguments'.
         */
        public static ExactAnswer<LinearForm<Quantity>> formOf(
                LinearForm<?> form, Map<LawNumber<?>, LinearForm<Quantity>> numbers) {
            List<LinearForm<Quantity>> scaled = new ArrayList<>();
            scaled.add(LinearForm.constant(form.constant()));
            Set<UnheldNumber> unheld = EnumSet.noneOf(UnheldNumber.class);
            form.coefs().forEach((number, weight) -> {
                switch (numbers.get(number).times(weight)) {
                    case ExactAnswer.Held<LinearForm<Quantity>>(var held) -> scaled.add(held);
                    case ExactAnswer.Unheld<LinearForm<Quantity>>(var why) -> unheld.add(why);
                }
            });
            // Every part's weights added at once, so whether they are held does not turn on which
            // came first; and where some are not, which way is said of all of them.
            return !unheld.isEmpty() ? ExactAnswer.unheld(UnheldNumber.ofAll(unheld))
                    : LinearForm.sum(scaled);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            LinearForm<Quantity> form = ((ExactAnswer.Held<LinearForm<Quantity>>)
                    formOf(part.form(), numbers)).value();
            if (form.coefs().isEmpty()) {
                return new Proposition.Always(part.states().holds(form.constant().signum()));
            }
            Relation.OneWay<Quantity> one = Relation.OneWay.of(form, part.states());
            return new AComparisonRead(ComparisonReading.BY_A_LAW,
                    new Relation.Affine(one.form(), one.proposition()), one.holds(), counts)
                    .conclusion(numbering);
        }
    }

    /**
     * The number an operation answering the order of its two arguments answered, compared as
     * {@code sign} says, read as the comparison of the two arguments that sign stands for.
     *
     * <p>Which comparison of the arguments it stands for is the operation's: the sign held to the
     * bounds the library states of what the operation answers
     * ({@link TheSignOfAnOrder#betweenTheArguments}). Where the two leave the arguments open, or
     * settle the comparison whatever they are, there is no order to read and the step is refused.
     *
     * <p>And it is of the two arguments the call has, as a reading of a law is of the call
     * ({@link ByALaw}): what it concludes names the positions the greater and the lesser stand at,
     * and no other, where they stand at positions.
     */
    record AnOrderOfItsArguments(TheCall call, TheSignOfAnOrder.TheSign sign,
                                 Derivation ofTheArguments) implements Derivation {

        public AnOrderOfItsArguments {
            Objects.requireNonNull(call, "an order is of the arguments of a call");
            Objects.requireNonNull(sign, "an order is answered by an operation");
            Objects.requireNonNull(ofTheArguments, "an order is of the arguments");
            if (TheSignOfAnOrder.betweenTheArguments(sign.operation(), sign.spacing(),
                    sign.written(), sign.against()) == null
                    || !call.operation().equals(sign.operation())) {
                throw new IllegalArgumentException(sign + " states no order of the arguments of "
                        + call.operation());
            }
            List<TermPath> roots = new ArrayList<>();
            for (DeclaredArgument each : TheSignOfAnOrder.orderedArguments(sign.operation())) {
                TermPath at = call.standingAt().get(each);
                if (at != null) {
                    roots.add(at);
                }
            }
            if (roots.size() == 2
                    && !ofTheArguments.concludes(Optional.empty()).staysWithin(roots)) {
                throw new IllegalArgumentException(ofTheArguments + " is no reading of the order of "
                        + call.standingAt());
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(ofTheArguments);
        }
    }

    /**
     * The number an operation answering the order of its two arguments answered, compared as
     * {@code sign} says, where every answer the library says it can give comes out the same way:
     * that way, worked out here from the bounds ({@link TheSignOfAnOrder#settledByItsBounds}).
     */
    record ASignItsBoundsSettle(TheSignOfAnOrder.TheSign sign) implements Derivation {

        public ASignItsBoundsSettle {
            Objects.requireNonNull(sign, "an order is answered by an operation");
            if (holds(sign) == null) {
                throw new IllegalArgumentException(sign + " is not the same on every answer");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds(sign));
        }

        private static Boolean holds(TheSignOfAnOrder.TheSign sign) {
            return TheSignOfAnOrder.settledByItsBounds(sign.operation(), sign.spacing(),
                    sign.written(), sign.against());
        }
    }

    /**
     * Some element of a container written out making a closure answer some way: some one of what
     * the closure's body states of each element, read on the application that hands it that
     * element — and nothing where none is written.
     */
    record OverElementsWrittenOut(List<Derivation> ofEach, boolean holds) implements Derivation {

        public OverElementsWrittenOut {
            ofEach = List.copyOf(ofEach);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> each = new ArrayList<>();
            for (Derivation one : ofEach) {
                Proposition answered = numbering.of(one);
                each.add(holds ? answered : answered.denied());
            }
            return Proposition.any(each);
        }
    }

    /**
     * A condition inside a closure applied to each of the values a container was written with, read
     * on each application: what it states on the one a run meets it on.
     */
    record OnEachApplication(List<Derivation> each) implements Derivation {

        public OnEachApplication {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("a condition is read on some application");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return Proposition.onAnApplication(each.stream().map(numbering::of).toList());
        }

        @Override
        public List<Derivation> oneOf() {
            return each;
        }
    }

    /**
     * Some element of the container at {@code container} meeting what the closure's body states of
     * it, with what no element decides taken out of the quantifier.
     *
     * <p>What comes out the same for every element is itself and there being an element at all — one
     * that never holds settles it, one that always does leaves whether there is an element. A
     * disjunct no element decides is that disjunct and there being an element, beside some element
     * meeting the rest; a conjunct is that conjunct, beside some element meeting the rest. Left
     * inside, whether the container holds anything would be something the proposition turns on that
     * none of its parts names, and a reader of the parts would hand nobody the container.
     *
     * @param holdsSomething that the container holds something, held only where the conclusion
     *                       has it as a part ({@link #asksWhetherItHoldsAnything})
     */
    record SomeElementMeeting(TermPath container, Derivation ofTheElement, boolean holds,
                              Optional<Derivation> holdsSomething) implements Derivation {

        public SomeElementMeeting {
            Objects.requireNonNull(container, "an element is of a container");
            Objects.requireNonNull(ofTheElement, "an element meets something");
            Objects.requireNonNull(holdsSomething, "whether it holds anything is read or not asked");
        }

        /**
         * Whether some element meeting {@code ofTheElement} has the container's holding anything as
         * a part.
         */
        public static boolean asksWhetherItHoldsAnything(TermPath container,
                                                         Proposition ofTheElement) {
            if (!ofTheElement.mayTurnOnAnElementOf(container)) {
                return !(ofTheElement instanceof Proposition.Always(boolean holds) && !holds);
            }
            if (!(ofTheElement instanceof Proposition.Any any)) {
                return false;
            }
            List<Proposition> decided = any.parts().stream()
                    .filter(part -> !part.mayTurnOnAnElementOf(container)).toList();
            return !decided.isEmpty()
                    && asksWhetherItHoldsAnything(container, Proposition.any(decided));
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition answered = numbering.of(ofTheElement);
            Proposition element = holds ? answered : answered.denied();
            return meeting(element, numbering);
        }

        private Proposition meeting(Proposition element, Conclusion numbering) {
            if (!element.mayTurnOnAnElementOf(container)) {
                return element instanceof Proposition.Always(boolean holds) && !holds
                        ? element
                        : Proposition.all(List.of(element, numbering.of(holdsSomething
                                .orElseThrow(() -> new IllegalStateException(
                                        "whether " + container + " holds anything is a part of"
                                                + " what is concluded and was not read")))));
            }
            List<Proposition> parts = switch (element) {
                case Proposition.All all -> all.parts();
                case Proposition.Any any -> any.parts();
                default -> List.of(element);
            };
            List<Proposition> decided = parts.stream()
                    .filter(part -> !part.mayTurnOnAnElementOf(container)).toList();
            if (decided.isEmpty()) {
                return new Proposition.Some(container, element, true);
            }
            List<Proposition> undecided = parts.stream()
                    .filter(part -> part.mayTurnOnAnElementOf(container)).toList();
            return element instanceof Proposition.Any
                    ? Proposition.any(List.of(meeting(Proposition.any(decided), numbering),
                            new Proposition.Some(container, Proposition.any(undecided), true)))
                    : Proposition.all(List.of(Proposition.all(decided),
                            new Proposition.Some(container, Proposition.all(undecided), true)));
        }
    }

    // The grounds: a part made from what one kind of thing says, and nothing else.

    /** A truth, a container's holding anything or an optional's holding a value, written out. */
    record WrittenOut(boolean holds) implements Derivation {

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds);
        }
    }

    /** A truth whose answer the language works out from values written out. */
    record Folded(boolean holds) implements Derivation {

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds);
        }
    }

    /**
     * A {@code Bool} a row controls, holding {@code held}: one at a position of the input, or one a
     * dependency answered.
     */
    record ATruthOfASubject(DecisionSubject of, boolean held) implements Derivation {

        public ATruthOfASubject {
            Objects.requireNonNull(of, "a truth is some subject's");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Truth(of, held);
        }
    }

    /** An optional a row controls holding a value. */
    record PresentInASubject(DecisionSubject of) implements Derivation {

        public PresentInASubject {
            Objects.requireNonNull(of, "an optional is some subject's");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Present(of, true);
        }
    }

    /** Whether a value a row controls is one of the cases an arm selects. */
    record CasesOfASubject(DecisionSubject of, CasesLeft cases) implements Derivation {

        public CasesOfASubject {
            Objects.requireNonNull(of, "a value is some subject's");
            Objects.requireNonNull(cases, "an arm selects some cases");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.InCases(of, cases, true);
        }
    }

    /** Whether every row takes an arm, settled by the cases the source wrote. */
    record CasesWrittenOut(boolean every) implements Derivation {

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(every);
        }
    }

    /** That a container at a position of the input holds something: its size above nought. */
    record SizeAboveNought(NumericTerm.TakenOf size) implements Derivation {

        public SizeAboveNought {
            Objects.requireNonNull(size, "a size is taken of something");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Compared(new Relation.Affine(
                    LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(size)), Rel.GT), true);
        }
    }

    /**
     * A comparison read as the relation it states, by the reading named — what the relation is is
     * that reading's answer, and this is where it entered.
     *
     * <p>A count of elements among its quantities was read too, and is held here as how: each count
     * the relation names is one of {@code counts}, concluded from the reading of what its elements
     * meet, and a count the relation names that none of these reads is refused where it is
     * concluded.
     */
    record AComparisonRead(ComparisonReading by, Relation relation, boolean holds,
                           List<Counted> counts)
            implements Derivation {

        public AComparisonRead(ComparisonReading by, Relation relation, boolean holds) {
            this(by, relation, holds, List.of());
        }

        public AComparisonRead {
            Objects.requireNonNull(by, "a comparison is read by something");
            Objects.requireNonNull(relation, "a comparison states a relation");
            counts = List.copyOf(counts);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Quantity> read = new ArrayList<>(counts.size());
            counts.forEach(count -> read.add(count.counted(numbering)));
            List<Quantity> named = switch (relation) {
                case Relation.Affine affine -> affine.form().coefs().keySet().stream()
                        .filter(quantity -> quantity instanceof Quantity.HowManyMeet).toList();
                case Relation.Ordered _ -> List.of();
            };
            if (!read.containsAll(named) || !named.containsAll(read)) {
                throw new IllegalStateException("a relation over " + named
                        + " is read from counts of " + read);
            }
            return Proposition.compared(relation, holds);
        }

        /**
         * How many elements of the container at {@code container} meet what {@code ofTheElement}
         * was read as.
         */
        public record Counted(TermPath container, Derivation ofTheElement) {

            public Counted {
                Objects.requireNonNull(container, "a count is of a container");
                Objects.requireNonNull(ofTheElement, "of the elements meeting something");
            }

            /** The count this reads. */
            public Quantity.HowManyMeet counted(Conclusion numbering) {
                return new Quantity.HowManyMeet(container, numbering.of(ofTheElement));
            }
        }
    }

    /** The readings a comparison is turned into a relation by. */
    enum ComparisonReading {

        /** A form over the input's numbers against a cut. */
        AS_A_CUT,

        /** A term of the input against a place on an order it stands on. */
        ON_AN_ORDER,

        /** A form over numbers of values the body bound. */
        OVER_BOUND_VALUES,

        /** A form over numbers of an operation's arguments, which its law states a comparison of. */
        BY_A_LAW
    }

    /** A {@code Bool} a row controls compared with a truth the source settles. */
    record ATruthCompared(DecisionSubject of, boolean held) implements Derivation {

        public ATruthCompared {
            Objects.requireNonNull(of, "a truth is some subject's");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Truth(of, held);
        }
    }

    /**
     * A comparison whose answer the arithmetic settles whatever the input.
     *
     * @param named the numbers of the input the comparison was read over, whether or not they
     *              survived the cancelling: {@code a - a <= 0} is about {@code a} and cuts nothing.
     *              Empty where the reading named none of the input's own
     */
    record ACutThatCutsNothing(boolean holds, Set<NumericTerm> named) implements Derivation {

        public ACutThatCutsNothing {
            named = Set.copyOf(named);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds);
        }
    }

    /** A part this reading took no step into, and why. */
    record Stopped(WhyUnread why, boolean fixed) implements Derivation {

        public Stopped {
            Objects.requireNonNull(why, "a reading stops for a reason");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.unread(this);
        }
    }
}
