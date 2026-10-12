package souther.compiler.meaning;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.TheSignOfAnOrder;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.semantics.TakenAs;
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
     * What is stated of an element of a container together with what the operations that kept it
     * stated of it: an element of what was kept is one of those it was handed that met each
     * statement it was kept by.
     */
    record OfWhatWasKept(Derivation ofTheElement, List<Derivation> kept) implements Derivation {

        public OfWhatWasKept {
            Objects.requireNonNull(ofTheElement, "an element has something stated of it");
            kept = List.copyOf(kept);
            if (kept.isEmpty()) {
                throw new IllegalArgumentException("an element was kept by some statement");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> each = new ArrayList<>();
            each.add(numbering.of(ofTheElement));
            kept.forEach(one -> each.add(numbering.of(one)));
            return Proposition.all(each);
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
     * What a recursive helper a call names answers, read off its body where the call stands: what
     * {@code inItsBody} states of the walk the body makes ({@link AcrossAWalk}).
     */
    record ARecursionsBody(ValueName.Helper helper, Derivation inItsBody) implements Derivation {

        public ARecursionsBody {
            Objects.requireNonNull(helper, "a call names a helper");
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

    /** An {@code if}: its arm under its condition, and its other arm under the denial of it — or
     *  what both state, where they state one thing. */
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
            if (yes.key().equals(no.key()) && Proposition.firstStopIn(yes) == null) {
                return yes;
            }
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
     *
     * <p>Some arm is taken whatever the value. A match covers its scrutinee, a choice between
     * constructing and not covers both, and the cases the library defines an operation or a size
     * in cover everything the operation is given.
     */
    record MatchArms(List<Arm> arms) implements Derivation {

        public MatchArms {
            if (arms == null || arms.isEmpty()) {
                throw new IllegalArgumentException("a match has an arm");
            }
            arms = List.copyOf(arms);
        }

        /**
         * One arm: whether it selects the value, and what it states once taken.
         *
         * @param aboutTheEntry whether the arm states something of the value of the entry that
         *                      selecting it picked out, so that what it states holds of that entry
         *                      and not of some other
         */
        public record Arm(Derivation selects, Derivation states, boolean aboutTheEntry) {

            public Arm {
                Objects.requireNonNull(selects, "an arm selects some values");
                Objects.requireNonNull(states, "an arm states something");
            }

            public Arm(Derivation selects, Derivation states) {
                this(selects, states, false);
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> selecting = new ArrayList<>(arms.size());
            List<Proposition> stating = new ArrayList<>(arms.size());
            for (Arm arm : arms) {
                selecting.add(numbering.of(arm.selects()));
                stating.add(numbering.of(arm.states()));
            }
            // Some arm is always taken, so where every arm states one thing that is what is
            // stated, whichever arm selects. Not where an arm's statement is about the entry it
            // picked out, which is a different entry under each arm.
            Proposition first = stating.getFirst();
            if (stating.stream().allMatch(each -> each.key().equals(first.key()))
                    && arms.stream().noneMatch(Arm::aboutTheEntry)
                    && Proposition.firstStopIn(first) == null) {
                return first;
            }
            List<Proposition> taken = new ArrayList<>();
            List<Proposition> before = new ArrayList<>();
            for (int i = 0; i < arms.size(); i++) {
                Arm arm = arms.get(i);
                Proposition selects = selecting.get(i);
                List<Proposition> arrives = new ArrayList<>(noArmBefore(before, selects));
                Proposition states = stating.get(i);
                // The entry an arm picks out is the one its statement is about: the statement
                // sits inside the quantifier that selected it, where its subjects under the
                // container's elements are that entry's.
                if (arm.aboutTheEntry() && selects instanceof Proposition.Some(
                        DecisionSubject container, Proposition ofTheEntry, boolean holds, var _)
                        && holds) {
                    arrives.add(new Proposition.Some(container,
                            Proposition.all(List.of(ofTheEntry, states)), true));
                } else {
                    arrives.add(selects);
                    arrives.add(states);
                }
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
            List<Proposition> earlier = before.stream().map(numbering::of).toList();
            Proposition selecting = numbering.of(selects);
            List<Proposition> arrives = new ArrayList<>(noArmBefore(earlier, selecting));
            arrives.add(selecting);
            return Proposition.all(arrives);
        }
    }

    /**
     * That none of the arms written before one selecting {@code selects} selects the value, as the
     * parts a value arriving at that arm meets: each of them denied, but an arm selecting cases of
     * the same subject that share none with the cases {@code selects} leaves, which every value it
     * selects is already outside.
     *
     * <p>A match over the cases of a sum, one case an arm, is then each arm's case and nothing
     * besides, rather than its case beside the denial of every case before it.
     */
    private static List<Proposition> noArmBefore(List<Proposition> before, Proposition selects) {
        List<Proposition> out = new ArrayList<>();
        for (Proposition each : before) {
            if (!apart(each, selects)) {
                out.add(each.denied());
            }
        }
        return out;
    }

    /** Whether no value both {@code one} and {@code other} select can be, by the cases of one
     *  subject each holds it to. */
    private static boolean apart(Proposition one, Proposition other) {
        return one instanceof Proposition.InCases(
                DecisionSubject of, CasesLeft cases, boolean holds, String _)
                && holds
                && other instanceof Proposition.InCases(
                        DecisionSubject same, CasesLeft chosen, boolean chosenHolds, String _)
                && chosenHolds && of.equals(same) && cases.meet(chosen) == null;
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
     * <p>And it is held to the call, in two things that are each their own obligation. Which
     * argument a step is of: where an argument stands is what {@code call} says, and a step that
     * reads a position for one — the container some element is of, the subject a side is observed
     * of — reads exactly the position the argument stands at, the position of an element of it or
     * of the key one is filed under where the law says so. And what is read of it: a side observed
     * is that side observed, and a number the law names is the number of its own kind — the
     * argument's own number, how many it holds, how many different values its elements come to,
     * how many meet a statement, what a number of each adds up to — so that one kind of an
     * argument's number is never taken for another of the same position. How an argument that
     * stands at no position is read, and what a closure states of an element, are the reading
     * rules' own and are held to nothing here.
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
                // What the operations that kept the element state of it is no part of the law.
                if (read instanceof OfWhatWasKept(Derivation ofTheElement, var _)) {
                    return reads(law, ofTheElement);
                }
                // And what a map filed from a list adds to the element each entry is.
                if (read instanceof OfTheLastToHoldItsValue(Derivation ofTheElement, var _,
                        var _)) {
                    return reads(law, ofTheElement);
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
                                    && part.equals(law) && observes(observed, seen);
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

            /**
             * Whether {@code read} joins a reading of each of {@code parts}, in order, as
             * {@code law} joins them — or, for an "or", of each part it did not leave out for
             * implying another ({@link ALawJoinsWithoutWhatImpliesAnother}, which holds what was
             * left out to that).
             */
            private boolean joins(LawProposition<DeclaredArgument> law,
                                  List<LawProposition<DeclaredArgument>> parts, Derivation read) {
                if (read instanceof ALawJoinsWithoutWhatImpliesAnother(var part, var each)) {
                    if (!part.equals(law)) {
                        return false;
                    }
                    for (int i = 0; i < parts.size(); i++) {
                        if (each.get(i) instanceof ALawJoinsWithoutWhatImpliesAnother.Disjunct
                                .Read(Derivation one) && !reads(parts.get(i), one)) {
                            return false;
                        }
                    }
                    return true;
                }
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
             * container was written with — or a step that states what one of the steps under it
             * states, a container chosen by cases or answered through a body, every one of which
             * is some element meeting it in its turn.
             */
            private boolean meets(LawProposition.SomeElement<DeclaredArgument> some,
                                  Derivation read) {
                return switch (read) {
                    case Stopped _ -> true;
                    // What the container holding something was read as is a reading of what made
                    // the container, held to that call where it was made.
                    case EveryElementMeetsIt(var part, var _, Derivation ofTheElement, var _) ->
                            part.equals(some) && reads(some.ofTheElement(), ofTheElement);
                    case SomeElementMeeting(DecisionSubject container, Derivation ofTheElement,
                                            boolean holds, var _) ->
                            holds && standsAt(some.container(), container)
                                    && reads(some.ofTheElement(), ofTheElement);
                    case SomePieceMeeting(var _, Derivation ofThePiece) ->
                            reads(some.ofTheElement(), ofThePiece);
                    case OverElementsWrittenOut(List<Derivation> ofEach, boolean holds) -> {
                        Set<DeclaredArgument> inside = new HashSet<>(writtenOut);
                        inside.add(some.container());
                        Standing within = new Standing(call, inside);
                        yield holds && ofEach.stream()
                                .allMatch(each -> within.reads(some.ofTheElement(), each));
                    }
                    default -> {
                        List<Derivation> oneOf = read.oneOf();
                        yield oneOf != null && !oneOf.isEmpty()
                                && oneOf.stream().allMatch(each -> meets(some, each));
                    }
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
                // The same statement of what the operation that made the string was handed, read
                // at that call and held to it there.
                if (read instanceof WhereAnOperationKeepsIt(var part, var _, var _)) {
                    return part.equals(law);
                }
                if (read instanceof ALawComparison leaf) {
                    return leaf.part().equals(law) && law.form().coefs().keySet().stream()
                            .allMatch(number -> numberStands(number, leaf.numbers().get(number),
                                    leaf));
                }
                List<Derivation> oneOf = read.oneOf();
                return oneOf != null && !oneOf.isEmpty()
                        && oneOf.stream().allMatch(each -> compares(law, each));
            }

            /** Whether the container {@code argument} is, read at {@code container}, stands
             *  there: at the position the call has it at, where it has it at one. */
            private boolean standsAt(DeclaredArgument argument, DecisionSubject container) {
                TermPath at = call.standingAt().get(argument);
                return at == null || new DecisionSubject.AnInput(at).equals(container);
            }

            /**
             * The position {@code argument} stands at, or null where a reading of it is held to
             * none: it stands at no position, or is read as the values it was written with.
             */
            private TermPath positionOf(DeclaredArgument argument) {
                return writtenOut.contains(argument) ? null : call.standingAt().get(argument);
            }

            /**
             * The position {@code subject} is, exactly: the argument's, an element of it, or the
             * key an element is filed under — or null where a reading of it is held to none. What a
             * closure answers is read in the closure's body, which stands at no position of the
             * call's.
             */
            private TermPath positionOf(LawSubject<DeclaredArgument> subject) {
                return switch (subject) {
                    case LawSubject.Argument<DeclaredArgument>(var argument) ->
                            positionOf(argument);
                    case LawSubject.ElementOf<DeclaredArgument>(var container) -> {
                        TermPath at = positionOf(container);
                        yield at == null ? null : at.element();
                    }
                    case LawSubject.KeyOf<DeclaredArgument>(var container) -> {
                        TermPath at = positionOf(container);
                        yield at == null ? null : at.key();
                    }
                    case LawSubject.WhatTheClosureAnswers<DeclaredArgument> _,
                         LawSubject.AnswerOf<DeclaredArgument> _ -> null;
                };
            }

            /**
             * Whether {@code seen} is exactly what observing the subject of {@code observed} on
             * its side says of the position the call has it at: that it is true, that it is
             * present, that it holds something.
             */
            private boolean observes(LawProposition.Observed<DeclaredArgument> observed,
                                     Derivation seen) {
                TermPath at = positionOf(observed.of());
                if (at == null) {
                    return true;
                }
                Proposition concluded = seen.concludes(Optional.empty());
                if (concluded instanceof Proposition.Unread) {
                    return true;
                }
                DecisionSubject subject = new DecisionSubject.AnInput(at);
                return switch (observed.side().aspect()) {
                    case TRUTH -> concluded.equals(
                            new ATruthOfASubject(subject, true).concludes(Optional.empty()));
                    case PRESENCE -> concluded.equals(
                            new PresentInASubject(subject).concludes(Optional.empty()));
                    case EMPTINESS -> concluded instanceof Proposition.Compared(
                            Relation.Affine(var form, var rel), boolean holds, var _)
                            && holds && rel == Rel.GT && howManyAt(soleAtom(form), at);
                };
            }

            /** Whether {@code read}, the subject {@code subject} was read as, is the position the
             *  call has it at. */
            private boolean stands(LawSubject<DeclaredArgument> subject, DecisionSubject read) {
                TermPath at = positionOf(subject);
                return at == null || read.equals(new DecisionSubject.AnInput(at));
            }

            /**
             * Whether {@code form}, what {@code number} was read as, is the number the law means
             * of the argument it names: the argument's own number, how many it holds, how many
             * different values its elements come to, how many of them meet a statement, what a
             * number of each adds up to. Each is a number of its own kind, and one kind read as
             * another is no reading of the law even where both are of the same position. And a
             * count of the elements that meet a statement is a count of those meeting the law's
             * statement: the way {@code leaf} read what the elements meet is a reading of it.
             */
            private boolean numberStands(LawNumber<DeclaredArgument> number,
                                         LinearForm<Quantity> form, ALawComparison leaf) {
                Quantity atom = soleAtom(form);
                return switch (number) {
                    case LawNumber.AnArgument<DeclaredArgument>(var argument) -> {
                        TermPath at = positionOf(argument);
                        yield at == null || new DecisionAtom.OfTheInput(
                                new NumericTerm.ValueOf(at)).equals(atom);
                    }
                    case LawNumber.SizeOf<DeclaredArgument>(var of) -> {
                        TermPath at = positionOf(of);
                        yield at == null || howManyAt(atom, at);
                    }
                    case LawNumber.CodePointsOf<DeclaredArgument>(var of, var counted) -> {
                        TermPath at = positionOf(of);
                        yield at == null || (atom instanceof DecisionAtom.OfTheInput(
                                NumericTerm term)
                                && term instanceof NumericTerm.CodePointClassCount count
                                && count.position().equals(at)
                                && count.counted().equals(counted));
                    }
                    case LawNumber.HowManyDifferent<DeclaredArgument>(var container, var each) -> {
                        TermPath at = positionOf(container);
                        TermPath element = positionOf(each);
                        yield at == null || element == null
                                || new Quantity.HowManyDifferent(new DecisionSubject.AnInput(at),
                                new DecisionSubject.AnInput(element)).equals(atom);
                    }
                    // A sum is held spread over the numbers of each element and how many elements
                    // there are ({@link Quantity.SumOver#over}), so what each element adds is
                    // taken back out of it and is the law's number of the element.
                    case LawNumber.SumOver<DeclaredArgument>(var container, var each) -> {
                        TermPath at = positionOf(container);
                        if (at == null) {
                            yield true;
                        }
                        LinearForm<Quantity> added = Quantity.SumOver.addedByEach(
                                new DecisionSubject.AnInput(at), form,
                                part -> howManyAt(part, at));
                        yield added != null && numberStands(each, added, leaf);
                    }
                    case LawNumber.HowManyMeet<DeclaredArgument>(var container, var statement) -> {
                        TermPath at = positionOf(container);
                        yield at == null || counts(statement, at, form, atom, leaf);
                    }
                };
            }

            /**
             * Whether {@code form}, with {@code atom} its one quantity, is how many elements of
             * the container at {@code at} meet {@code statement}, as {@code leaf} read it: the
             * count of the elements meeting what was read as the statement, or, where every element
             * settles the statement alike, all of them or none.
             */
            private boolean counts(LawProposition<DeclaredArgument> statement, TermPath at,
                                   LinearForm<Quantity> form, Quantity atom, ALawComparison leaf) {
                Conclusion asked = new Conclusion(Optional.empty());
                DecisionSubject container = new DecisionSubject.AnInput(at);
                if (atom instanceof Quantity.HowManyMeet(DecisionSubject counted, var _)) {
                    return counted.equals(container) && leaf.counts().stream().anyMatch(count ->
                            count.container().equals(container)
                                    && atom.equals(count.counted(asked))
                                    && reads(statement, count.ofTheElement()));
                }
                return leaf.alike().stream().anyMatch(count -> count.container().equals(container)
                        && reads(statement, count.ofTheElement())
                        && count.ofTheElement().concludes(Optional.empty())
                        instanceof Proposition.Always(boolean all)
                        && (all ? howManyAt(atom, at)
                        : form.coefs().isEmpty() && form.constant().signum() == 0));
            }

            /** The one quantity {@code form} is, once, or null where it is anything else. */
            private static Quantity soleAtom(LinearForm<Quantity> form) {
                if (form.coefs().size() != 1 || form.constant().signum() != 0) {
                    return null;
                }
                Map.Entry<Quantity, ExactRatio> only = form.coefs().entrySet().iterator().next();
                return ExactRatio.ONE.equals(only.getValue()) ? only.getKey() : null;
            }

            /** Whether {@code atom} is how many what stands at {@code at} holds. */
            private static boolean howManyAt(Quantity atom, TermPath at) {
                return atom instanceof DecisionAtom.OfTheInput(
                        NumericTerm.TakenOf taken) && taken.position().equals(at)
                        && DefaultBoundOperationFacts.get().takenAs(taken.operation())
                        instanceof TakenAs.HowManyItHolds;
            }
        }
    }

    /** A step that reads one part of a law, which it holds. */
    sealed interface ALawPart extends Derivation
            permits ALawSettles, ALawJoins, OnTheSideALawNames, TheSameValue, ALawQuantifies,
                    ALawComparison, ALawJoinsWithoutWhatImpliesAnother, WhereAnOperationKeepsIt {

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
     * @param counts how each count the numbers needed was read: what the elements counted meet, as
     *               {@link AComparisonRead} holds it. The ones the form still names are held to
     *               it there; a count on both sides comes to nought and names none
     * @param alike  how each count every element settles alike was read: the statement came out
     *               the same for each, so the count is all of the container or none of it
     * @param mostChoices how many choices of which statements hold the reading writes the
     *                    comparison out as ({@link AComparisonRead})
     */
    record ALawComparison(LawProposition.Compared<?> part,
                          Map<LawNumber<?>, LinearForm<Quantity>> numbers,
                          List<AComparisonRead.Counted> counts,
                          List<AComparisonRead.Counted> alike,
                          long mostChoices)
            implements ALawPart {

        /**
         * {@code part} with its numbers read as {@code numbers}, the counts they needed read as
         * {@code counting} and {@code alike}.
         */
        public static ALawComparison of(LawProposition.Compared<?> part,
                                        Map<LawNumber<?>, LinearForm<Quantity>> numbers,
                                        Map<Quantity.HowManyMeet, AComparisonRead.Counted>
                                                counting,
                                        List<AComparisonRead.Counted> alike,
                                        long mostChoices) {
            return new ALawComparison(part, numbers, List.copyOf(counting.values()), alike,
                    mostChoices);
        }

        /**
         * The relation {@code part} states over {@code numbers}, faced the one way, or null where
         * the numbers cancel and it is settled.
         *
         * @throws IllegalArgumentException where the form is over numbers it cannot hold
         */
        public static Relation.OneWay<Quantity> relationOf(
                LawProposition.Compared<?> part, Map<LawNumber<?>, LinearForm<Quantity>> numbers) {
            if (!(formOf(part.form(), numbers)
                    instanceof ExactAnswer.Held<LinearForm<Quantity>>(LinearForm<Quantity> form))) {
                throw new IllegalArgumentException("a comparison over numbers it cannot hold is"
                        + " stopped at, and not read: " + part);
            }
            return form.coefs().isEmpty() ? null : Relation.OneWay.of(form, part.states());
        }

        public ALawComparison {
            Objects.requireNonNull(part, "a step reads a part of a law");
            numbers = Map.copyOf(numbers);
            counts = List.copyOf(counts);
            alike = List.copyOf(alike);
            if (!numbers.keySet().equals(part.form().coefs().keySet())) {
                throw new IllegalArgumentException("a comparison over " + part.form().coefs()
                        .keySet() + " is read with " + numbers.keySet());
            }
            Relation.OneWay<Quantity> one = relationOf(part, numbers);
            if (one != null && AComparisonRead.pastTheChoicesRead(
                    new Relation.Affine(one.form(), one.proposition()), mostChoices)) {
                throw new IllegalArgumentException("a comparison written out as more choices than"
                        + " are read is stopped at, and not read: " + part);
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
            Relation.OneWay<Quantity> one = relationOf(part, numbers);
            if (one == null) {
                LinearForm<Quantity> form = ((ExactAnswer.Held<LinearForm<Quantity>>)
                        formOf(part.form(), numbers)).value();
                return new Proposition.Always(part.states().holds(form.constant().signum()));
            }
            // The counts the relation still names: one on both sides came to nought and names none.
            Conclusion asked = new Conclusion(Optional.empty());
            List<AComparisonRead.Counted> named = counts.stream()
                    .filter(count -> one.form().coefs().containsKey(count.counted(asked)))
                    .toList();
            return new AComparisonRead(ComparisonReading.BY_A_LAW,
                    new Relation.Affine(one.form(), one.proposition()), one.holds(), named,
                    mostChoices).conclusion(numbering);
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
     * <p>And what it concludes is that order of the two arguments the call has, as a reading of a
     * law is of the call ({@link ByALaw}): the greater standing as the sign says to the lesser,
     * where both stand at positions, and no other relation between them or of either to anything
     * else.
     */
    record AnOrderOfItsArguments(TheCall call, TheSignOfAnOrder.TheSign sign,
                                 Derivation ofTheArguments) implements Derivation {

        public AnOrderOfItsArguments {
            Objects.requireNonNull(call, "an order is of the arguments of a call");
            Objects.requireNonNull(sign, "an order is answered by an operation");
            Objects.requireNonNull(ofTheArguments, "an order is of the arguments");
            Rel between = TheSignOfAnOrder.betweenTheArguments(sign.operation(), sign.spacing(),
                    sign.written(), sign.against());
            if (between == null || !call.operation().equals(sign.operation())) {
                throw new IllegalArgumentException(sign + " states no order of the arguments of "
                        + call.operation());
            }
            List<DeclaredArgument> ordered = TheSignOfAnOrder.orderedArguments(sign.operation());
            TermPath greater = call.standingAt().get(ordered.get(0));
            TermPath lesser = call.standingAt().get(ordered.get(1));
            if (greater != null && lesser != null) {
                Proposition read = ofTheArguments.concludes(Optional.empty());
                if (!(read instanceof Proposition.Unread)
                        && !read.equals(theGreaterAgainstTheLesser(greater, lesser, between))) {
                    throw new IllegalArgumentException(ofTheArguments + " is not the order the"
                            + " library states of " + call.standingAt() + ": the greater " + between
                            + " the lesser");
                }
            }
        }

        /**
         * What the order says of the numbers at the two positions: the one at {@code greater}
         * standing {@code between} to the one at {@code lesser}. Where the two are one position
         * their difference is nought, and what is said is whether nought stands so to nought.
         */
        private static Proposition theGreaterAgainstTheLesser(TermPath greater, TermPath lesser,
                                                               Rel between) {
            LinearForm<Quantity> apart = LinearForm.difference(
                    new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(greater)),
                    new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(lesser)));
            if (apart.coefs().isEmpty()) {
                return new Proposition.Always(between.holds(apart.constant().signum()));
            }
            Relation.OneWay<Quantity> one = Relation.OneWay.of(apart, between);
            return Proposition.compared(new Relation.Affine(one.form(), one.proposition()),
                    one.holds());
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
    record SomeElementMeeting(DecisionSubject container, Derivation ofTheElement, boolean holds,
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
        public static boolean asksWhetherItHoldsAnything(DecisionSubject container,
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

    /**
     * What a walk from a seed ends with, coming out on the side asked of it, read by induction over
     * the elements walked: the step keeps what it carried where that came out one way, so the end
     * comes out that way where the seed did or where the step's answer on some element did.
     *
     * <p>A recursion over a list by its head is such a walk taken from the other end: what it
     * answers on the rest is what the step is carried, and what it answers on a list holding
     * nothing is the seed.
     *
     * <p>Read as a step whose answer {@code F} turns on what it was carried only through that
     * coming out on the same side. Where {@code F} holds whenever what was carried does, {@code F}
     * is what it is where nothing held carried, or what was carried: so the end holds where the
     * seed does or some element meets the step carried nothing that held ({@link
     * ConditionJoin#EITHER}). Where {@code F} fails whenever what was carried does, the end holds
     * where the seed does and every element meets the step carried something that held ({@link
     * ConditionJoin#BOTH}) — no element failing it, which is what {@code walked} states denied.
     *
     * <p>Whether the walk ends, and in what order it hands the elements, is not a premise. Each
     * element is walked once, and a run that does not end comes to no answer to be read.
     *
     * @param seed     what the seed comes out as
     * @param walked   some element meeting the step's answer on it: carried nothing that held,
     *                 where {@code how} is either; carried something that held and denied, where it
     *                 is both
     * @param keeps    the step's answer on the other of the two, which comes out as what was
     *                 carried whatever the element is, and is what lets the walk be read so
     * @param how      which of the two the step keeps
     */
    record AcrossAWalk(Derivation seed, SomeElementMeeting walked, Derivation keeps,
                       ConditionJoin how) implements Derivation {

        public AcrossAWalk {
            Objects.requireNonNull(seed, "a walk starts from a seed");
            Objects.requireNonNull(walked, "and walks the elements of something");
            Objects.requireNonNull(keeps, "with a step that keeps what it carried");
            Objects.requireNonNull(how, "one way or the other");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition start = numbering.of(seed);
            Proposition some = numbering.of(walked);
            return switch (how) {
                case EITHER -> Proposition.any(List.of(start, some));
                case BOTH -> Proposition.all(List.of(start, some.denied()));
            };
        }
    }

    /**
     * What a search from a node answers, coming out on the side asked of it, read by induction over
     * the nodes below it: some node reachable from it meeting what the body states with every call
     * of itself supposed to have come out the other way ({@link Proposition.SomeReachable}).
     *
     * <p>The body is read twice. Read with every call it makes of itself on a node below supposed
     * to have come out the way that leaves the answer to the node itself, it is what a node has to
     * meet ({@code atANode}). Read with each of those calls standing for the search from the node it
     * is on ({@link AReachedNode}), it is {@code unfoldedOnce}, which was found to be the node
     * meeting that or some node below it from which the search does, whatever its parts are
     * ({@link #unfoldsOnce}). Each call goes to an element of a container the node holds, so a run
     * goes down a finite value, and where it ends every call it made answered what the search from
     * its node does: the search is the least such answer, and the one the run gives.
     *
     * <p>Where {@code how} is {@link ConditionJoin#BOTH} it is read the other way round: the calls
     * supposed to have held, and the answer holding where every reachable node meets that — no node
     * failing it.
     *
     * @param node          where the node the search is from stands
     * @param through       the fields of a node whose elements are the nodes below it
     * @param atANode       the body with every call of itself supposed to have come out the way that
     *                      leaves the answer to the node: failed where {@code how} is either, held
     *                      where it is both
     * @param below         whether each container under {@code through} on the node holds
     *                      something, where each is measured
     * @param unfoldedOnce  the body with each call of itself standing for the search from its node
     * @param how           which side a call of itself coming out the other way leaves to the node
     */
    record ATreeSearched(TermPath node, List<String> through, Derivation atANode,
                         Optional<List<Derivation>> below, Derivation unfoldedOnce,
                         ConditionJoin how) implements Derivation {

        public ATreeSearched {
            Objects.requireNonNull(node, "a search is from a node");
            through = List.copyOf(through);
            Objects.requireNonNull(atANode, "of what a node meets");
            below = below.map(List::copyOf);
            Objects.requireNonNull(unfoldedOnce, "found by reading the body one step down");
            Objects.requireNonNull(how, "one way or the other");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition read = numbering.of(atANode);
            Optional<Proposition> noneBelow = below.map(each -> Proposition.all(each.stream()
                    .map(one -> numbering.of(one).denied()).toList()));
            return searchFrom(node, node, through, read, noneBelow, how);
        }

        /**
         * Whether {@code unfolded}, the body read with each call of itself on a node below standing
         * for the search from there, says what the search from the node at {@code node} does one
         * step down, whatever its parts are: the node meeting {@code atANode} or some node below
         * from which the search does — or, the other way round, the node meeting it and every node
         * below doing so.
         *
         * <p>Which quantifier a container of nodes below is read under is part of what is compared:
         * some node below and every node below are two parts, and one is never taken for the other.
         */
        public static boolean unfoldsOnce(Proposition unfolded, Proposition atANode, TermPath node,
                                          List<String> through, ConditionJoin how) {
            List<Proposition> parts = new ArrayList<>();
            parts.add(atANode);
            for (String field : through) {
                Proposition reached = searchFrom(node.then(field).element(), node, through,
                        atANode, Optional.empty(), how);
                DecisionSubject nodes = new DecisionSubject.AnInput(node.then(field));
                parts.add(switch (how) {
                    case EITHER -> new Proposition.Some(nodes, reached, true);
                    case BOTH -> new Proposition.Some(nodes, reached.denied(), false);
                });
            }
            Proposition expected = switch (how) {
                case EITHER -> Proposition.any(parts);
                case BOTH -> Proposition.all(parts);
            };
            return TruthTable.holdsWhateverItsPartsAre(Proposition.any(List.of(
                    Proposition.all(List.of(unfolded, expected)),
                    Proposition.all(List.of(unfolded.denied(), expected.denied())))));
        }
    }

    /**
     * A call a search makes of itself on a node below the one it is from, standing for the search
     * from there while the body is read one step down ({@link ATreeSearched}).
     *
     * @param at       where the node the call is on stands
     * @param from     where the node the search is read from stands
     * @param through  the fields of a node whose elements are the nodes below it
     * @param atANode  the body with every call of itself supposed to have come out the way that
     *                 leaves the answer to the node
     * @param how      which side that is
     */
    record AReachedNode(TermPath at, TermPath from, List<String> through, Derivation atANode,
                        ConditionJoin how) implements Derivation {

        public AReachedNode {
            Objects.requireNonNull(at, "a call is on a node");
            Objects.requireNonNull(from, "below the one the search is read from");
            through = List.copyOf(through);
            Objects.requireNonNull(atANode, "of what a node meets");
            Objects.requireNonNull(how, "one way or the other");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return searchFrom(at, from, through, numbering.of(atANode), Optional.empty(), how);
        }
    }

    /** The search from the node at {@code at} coming out as the body read with every call of itself
     *  supposed to have come out the way {@code how} leaves to the node, {@code read}, says. */
    private static Proposition searchFrom(TermPath at, TermPath writtenAt, List<String> through,
                                          Proposition read, Optional<Proposition> noneBelow,
                                          ConditionJoin how) {
        return switch (how) {
            case EITHER -> new Proposition.SomeReachable(at, writtenAt, through, read, noneBelow,
                    true);
            case BOTH -> new Proposition.SomeReachable(at, writtenAt, through, read.denied(),
                    noneBelow, false);
        };
    }

    // The grounds: a part made from what one kind of thing says, and nothing else.

    /** A truth, a container's holding anything or an optional's holding a value, written out. */
    record WrittenOut(boolean holds) implements Derivation {

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds);
        }
    }

    /**
     * What a walk carried into its step, on the side the walk's end is asked about: what the
     * concluding supposes it came out as ({@link Supposing}), and a part nothing read where it
     * supposes nothing of it.
     */
    record WhatAWalkCarried(ACarriedValue carried) implements Derivation {

        public WhatAWalkCarried {
            Objects.requireNonNull(carried, "a walk carried something");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.carried(carried);
        }
    }

    /**
     * What {@code step} states where what a walk carried into it came out as {@code holds}: the
     * step read once, and concluded under each way its walk needs it ({@link AcrossAWalk}).
     */
    record Supposing(Derivation step, ACarriedValue carried, boolean holds) implements Derivation {

        public Supposing {
            Objects.requireNonNull(step, "something is read under a supposition");
            Objects.requireNonNull(carried, "of something a walk carried");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.supposing(carried, holds).of(step);
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

    /**
     * What is stated of the value of an entry a lookup answered, and with it what picked the entry
     * out: that the element stated of is the one under the key asked for.
     *
     * <p>A statement about an entry's value is about the one entry the lookup answered. Said alone
     * it is about every element of the container, and a row would stand at it through an element
     * the lookup never reaches.
     *
     * @param selection whether the lookup answered a value, read as the quantifier it is: some
     *                  element holds the key
     * @param about     what is stated of the value
     */
    record OfTheEntryUnderTheKey(Derivation selection, Derivation about) implements Derivation {

        public OfTheEntryUnderTheKey {
            Objects.requireNonNull(selection, "an entry is picked out by a lookup");
            Objects.requireNonNull(about, "something is stated of the entry");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition stated = numbering.of(about);
            return numbering.of(selection) instanceof Proposition.Some(
                    DecisionSubject _, Proposition ofTheEntry, boolean holds, var _) && holds
                    ? Proposition.all(List.of(stated, ofTheEntry)) : stated;
        }
    }

    /**
     * What is stated of an element, where the element is the last of the container's to hold the
     * value it holds at {@code position}: what a map filed from a list holds under a key is the
     * element that came last of those the key was made of, so what is said of an entry is said
     * of that one.
     */
    record OfTheLastToHoldItsValue(Derivation ofTheElement, TermPath container,
                                   TermPath position) implements Derivation {

        public OfTheLastToHoldItsValue {
            Objects.requireNonNull(ofTheElement, "something is stated of the element");
            Objects.requireNonNull(container, "a last is of some container's elements");
            Objects.requireNonNull(position, "an element is told apart by some place");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return Proposition.all(List.of(numbering.of(ofTheElement),
                    new Proposition.LastToHold(container, position, true)));
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
            // Whether an optional holds a value is one fact however the arm that selects it was
            // written, so it is the statement a row answers of its own values.
            if (cases.only() instanceof Refinement.Presence presence) {
                return new Proposition.Present(of, presence.present());
            }
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

    /**
     * That a container holds something: its size above nought. The container is one at a position
     * of the input or one a dependency answered, and the size is the count of either.
     */
    record SizeAboveNought(DecisionAtom size) implements Derivation {

        public SizeAboveNought {
            Objects.requireNonNull(size, "a size is taken of something");
            if (size instanceof DecisionAtom.OfTheInput(var term)
                    && !(term instanceof NumericTerm.TakenOf)) {
                throw new IllegalArgumentException(size + " is no size of a container");
            }
            if (size instanceof DecisionAtom.OfAnAnswer) {
                throw new IllegalArgumentException(size + " is no size of a container");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Compared(new Relation.Affine(
                    LinearForm.<Quantity>atom(size), Rel.GT), true);
        }
    }

    /**
     * That some piece of a string, parted at one code point, holds a code point of a class: the
     * string holding one that is in the class and is not that code point.
     *
     * <p>The pieces together hold every code point of the string but the separator, so one of them
     * holds a code point of the class exactly where the string does. What the piece was read as is
     * kept, and is held to be that and nothing more: a statement about a piece that is not the
     * existence of such a code point — how many it holds, that it holds none — is no statement about
     * the string, and is not concluded here.
     *
     * @param counted the count of the string's code points that are in the class and are not the
     *                separator, which is what the pieces holding one comes to
     * @param ofThePiece what was read of a piece: that it holds a code point of the class
     */
    record SomePieceMeeting(NumericTerm.CodePointClassCount counted, Derivation ofThePiece)
            implements Derivation {

        public SomePieceMeeting {
            Objects.requireNonNull(counted, "the pieces' code points are counted of a string");
            Objects.requireNonNull(ofThePiece, "a piece is read as holding some code point");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Compared(new Relation.Affine(
                    LinearForm.<Quantity>atom(new DecisionAtom.OfTheInput(counted)), Rel.GT),
                    true);
        }

        @Override
        public List<Derivation> oneOf() {
            return List.of(ofThePiece);
        }
    }

    /**
     * Some element of what {@code operation} answered meeting what {@code part} asks of it, where
     * that comes out the same for every element: {@code ofTheElement} is it read of an element
     * known only by the side every element of the answer comes out on, and it settles one way.
     * Some element meets it exactly where the answer holds something, read as
     * {@code holdsSomething}, and it holds.
     *
     * <p>Whether the statement is written of the element ({@code w} holds something) or of what a
     * closure answers on it ({@code w -> Bool.not(String.isEmpty(w))}) is no part of this: both
     * are read of the same element. A statement it does not settle — how long a word is — is no
     * statement this reads.
     */
    record EveryElementMeetsIt(LawProposition.SomeElement<?> part, ValueName operation,
                               Derivation ofTheElement, Derivation holdsSomething)
            implements Derivation {

        public EveryElementMeetsIt {
            Objects.requireNonNull(part, "some element meets a statement");
            Objects.requireNonNull(operation, "of what an operation answered");
            Objects.requireNonNull(ofTheElement, "which is read of an element of it");
            Objects.requireNonNull(holdsSomething, "which is read as holding something");
            if (DefaultBoundOperationFacts.get().everyElementOfItsAnswerIs(operation) == null) {
                throw new IllegalArgumentException(operation
                        + " says nothing of every element of what it answers");
            }
            if (!(ofTheElement.concludes(Optional.empty()) instanceof Proposition.Always)) {
                throw new IllegalArgumentException(ofTheElement
                        + " comes out differently for different elements");
            }
        }

        /** Whether {@code part} asks of the element of its container the side every element of
         *  what {@code operation} answers comes out on. */
        public static boolean askedOfEveryElement(LawProposition.SomeElement<?> part,
                                                  ValueName operation) {
            return DefaultBoundOperationFacts.get().everyElementOfItsAnswerIs(operation)
                    instanceof SideAnswered side
                    && part.ofTheElement() instanceof LawProposition.Observed<?>(
                            LawSubject.ElementOf<?>(var container), SideAnswered asked)
                    && container.equals(part.container()) && asked.equals(side);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return Proposition.all(List.of(numbering.of(holdsSomething),
                    numbering.of(ofTheElement)));
        }
    }

    /**
     * An element of what {@code operation} answered coming out on {@code side}'s holding side, which
     * is the side every element of that answer comes out on: the answer {@code side} says.
     *
     * <p>The side is the operation's, taken from what is bound of it and never handed in.
     */
    record OfAnElementOfAnAnswer(ValueName operation, SideAnswered side) implements Derivation {

        public OfAnElementOfAnAnswer {
            Objects.requireNonNull(operation, "an element of what an operation answered");
            Objects.requireNonNull(side, "comes out on a side");
            if (!side.equals(DefaultBoundOperationFacts.get().everyElementOfItsAnswerIs(
                    operation))) {
                throw new IllegalArgumentException(operation
                        + " says no element of what it answers comes out " + side);
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(side.holds());
        }
    }

    /**
     * A part of a law joining its parts by "or", read without the parts that each imply another of
     * them: the "or" of the rest is the same statement, and that is what this concludes.
     *
     * <p>A part is left out where it holds only where a container an argument stands for holds
     * something, and another part, read here, is some element of that container meeting what
     * every element of it — what an operation answered — meets. Wherever the first holds the
     * container has an element, that element meets it, and the second holds; so the first adds
     * nothing to the "or". Which part implies which, and by what, is held here, and what is
     * concluded is the whole "or", never a part on its own.
     *
     * @param each for each part of {@code part}, in its order, its reading or what it implies
     */
    record ALawJoinsWithoutWhatImpliesAnother(LawProposition.Any<?> part, List<Disjunct> each)
            implements ALawPart {

        /** One part of the "or": read, or left out for implying another. */
        public sealed interface Disjunct {

            /** A part read as {@code read}. */
            record Read(Derivation read) implements Disjunct {

                public Read {
                    Objects.requireNonNull(read, "a part kept is read");
                }
            }

            /** A part left out: it implies {@code implied}, some element of what
             *  {@code operation} answered meeting what every element of that meets. */
            record ImpliesAnother(LawProposition.SomeElement<?> implied, ValueName operation)
                    implements Disjunct {

                public ImpliesAnother {
                    Objects.requireNonNull(implied, "a part left out implies another");
                    Objects.requireNonNull(operation, "by what an operation answers");
                }
            }
        }

        public ALawJoinsWithoutWhatImpliesAnother {
            Objects.requireNonNull(part, "a step reads a part of a law");
            each = List.copyOf(each);
            if (each.size() != part.parts().size()) {
                throw new IllegalArgumentException("a law joining " + part.parts().size()
                        + " statements is read as " + each.size());
            }
            boolean leftOut = false;
            for (int i = 0; i < each.size(); i++) {
                if (each.get(i) instanceof Disjunct.ImpliesAnother(var implied, var operation)) {
                    int at = part.parts().indexOf(implied);
                    if (at < 0 || !(each.get(at) instanceof Disjunct.Read) || !implied.holds()
                            || !EveryElementMeetsIt.askedOfEveryElement(implied, operation)
                            || !holdsOnlyWhereItHoldsSomething(part.parts().get(i),
                                    implied.container())) {
                        throw new IllegalArgumentException(part.parts().get(i)
                                + " does not imply a part of " + part + " that is read");
                    }
                    leftOut = true;
                }
            }
            if (!leftOut) {
                throw new IllegalArgumentException("an \"or\" read whole is joined as it is");
            }
        }

        /**
         * Whether {@code part} holds only where {@code container} holds something: it is, or
         * joins with "and", a comparison of how many {@code container} holds alone that fails
         * where it holds none.
         */
        public static boolean holdsOnlyWhereItHoldsSomething(LawProposition<?> part,
                                                             Object container) {
            return switch (part) {
                case LawProposition.All<?>(var parts) -> parts.stream()
                        .anyMatch(each -> holdsOnlyWhereItHoldsSomething(each, container));
                case LawProposition.Compared<?>(var form, Rel states) ->
                        form.coefs().size() == 1 && form.coefs().containsKey(
                                new LawNumber.SizeOf<>(new LawSubject.Argument<>(container)))
                                && !states.holds(form.constant().signum());
                default -> false;
            };
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> kept = new ArrayList<>();
            for (Disjunct one : each) {
                if (one instanceof Disjunct.Read(Derivation read)) {
                    kept.add(numbering.of(read));
                }
            }
            return Proposition.any(kept);
        }
    }

    /**
     * A part of a law that says only whether a string holds a code point of a class — the same for
     * every count of them of one or more — where the string is what {@code operation} answered, and
     * that holds one exactly where its argument does: read as {@code ofWhatItWasHanded}, the same
     * statement of that argument at the call of {@code operation}.
     */
    record WhereAnOperationKeepsIt(LawProposition.Compared<?> part, ValueName operation,
                                   Derivation ofWhatItWasHanded) implements ALawPart {

        public WhereAnOperationKeepsIt {
            Objects.requireNonNull(part, "a step reads a part of a law");
            Objects.requireNonNull(operation, "about what an operation answers");
            Objects.requireNonNull(ofWhatItWasHanded, "read of what it was handed");
            CodePointClass counted = whetherItHoldsOne(part);
            if (counted == null || !(DefaultBoundOperationFacts.get()
                    .keepsWhetherItHoldsACodePointOf(operation)
                    instanceof BoundOperationFacts.KeptCodePoints kept)
                    || !kept.counted().equals(counted)) {
                throw new IllegalArgumentException(part + " is not kept by " + operation);
            }
        }

        /**
         * The class {@code part} asks whether a string holds a code point of, where it says that
         * and nothing more — or null where it says anything else.
         *
         * <p>A relation over the one count: it comes out one way at none and the other at one, and
         * as at one at two. A relation over one number that does is the same at every count of one
         * or more, since a half-line, one point or all but one point that parts nought from one and
         * not one from two parts nought from everything above it.
         */
        public static CodePointClass whetherItHoldsOne(LawProposition.Compared<?> part) {
            if (part.form().coefs().size() != 1) {
                return null;
            }
            Map.Entry<? extends LawNumber<?>, ExactRatio> only =
                    part.form().coefs().entrySet().iterator().next();
            if (!(only.getKey() instanceof LawNumber.CodePointsOf<?>(
                    LawSubject.Argument<?> _, CodePointClass counted))) {
                return null;
            }
            boolean[] holds = new boolean[3];
            for (int count = 0; count < holds.length; count++) {
                ExactRatio value = only.getValue().times(ExactRatio.of(count))
                        .flatMap(part.form().constant()::plus).orNull();
                if (value == null) {
                    return null;
                }
                holds[count] = part.states().holds(value.signum());
            }
            return holds[0] != holds[1] && holds[1] == holds[2] ? counted : null;
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(ofWhatItWasHanded);
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
     *
     * <p>Every comparison a reading concludes enters here, so this is where a count of statements
     * about values written out is held to how many choices of which hold one condition is read in
     * ({@link WhichOfThemHold}). One that would be written out as more is stopped at by the reading
     * and never made.
     *
     * @param mostChoices how many choices of which statements hold the reading writes one
     *                    comparison out as
     */
    record AComparisonRead(ComparisonReading by, Relation relation, boolean holds,
                           List<Counted> counts, long mostChoices)
            implements Derivation {

        public AComparisonRead(ComparisonReading by, Relation relation, boolean holds,
                               long mostChoices) {
            this(by, relation, holds, List.of(), mostChoices);
        }

        public AComparisonRead {
            Objects.requireNonNull(by, "a comparison is read by something");
            Objects.requireNonNull(relation, "a comparison states a relation");
            counts = List.copyOf(counts);
            if (pastTheChoicesRead(relation, mostChoices)) {
                throw new IllegalArgumentException("a comparison written out as more choices than"
                        + " are read is stopped at, and not read: " + relation);
            }
        }

        /** Whether {@code relation} is a count of statements written out as more than
         *  {@code mostChoices} choices of which of them hold. */
        public static boolean pastTheChoicesRead(Relation relation, long mostChoices) {
            return Proposition.choicesIn(relation, mostChoices) > mostChoices;
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
            return Proposition.compared(relation, holds, mostChoices);
        }

        /**
         * How many elements of the container at {@code container} meet what {@code ofTheElement}
         * was read as.
         */
        public record Counted(DecisionSubject container, Derivation ofTheElement) {

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
