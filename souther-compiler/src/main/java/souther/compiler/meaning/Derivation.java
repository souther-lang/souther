package souther.compiler.meaning;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
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
    }

    /**
     * An arm of a {@code match} entered: it selects the value, and no arm written before it does.
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
    }

    /**
     * What a behavior's body states over its own parameters, at one call of it: each place of its
     * input moved to the same way into what the call handed that parameter ({@link MovedToACall}).
     * The body's statement is read once, of the definition; this is the one step that is the
     * call's.
     *
     * @param handed which position of the caller's input each parameter was handed, by the name the
     *               body reads it by; a parameter handed anything else is not in it
     */
    record ABehaviorsAnswerAtACall(ValueName.Behavior behavior, Derivation inItsBody,
                                   Map<String, TermPath> handed) implements Derivation {

        public ABehaviorsAnswerAtACall {
            Objects.requireNonNull(behavior, "a call is of some behavior");
            Objects.requireNonNull(inItsBody, "a body states something");
            handed = Map.copyOf(handed);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return MovedToACall.of(numbering.of(inItsBody), handed,
                    why -> numbering.unread(new Stopped(why, false)));
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
    }

    /**
     * The cases the library writes {@code operation}'s definition in: a case is taken where its
     * arguments stand as it says and none before it, and what is stated is what the case taken
     * states. The library's cases cover everything the operation can be given, which is what makes
     * the choice between them the operation.
     */
    record AnOperationsCases(ValueName.Stdlib operation, List<MatchArms.Arm> cases)
            implements Derivation {

        public AnOperationsCases {
            Objects.requireNonNull(operation, "cases are an operation's");
            if (cases == null || cases.isEmpty()) {
                throw new IllegalArgumentException("an operation defined by cases has a case");
            }
            cases = List.copyOf(cases);
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new MatchArms(cases).conclusion(numbering);
        }
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
     * An operation whose answer comes out on {@code aspect}'s holding side exactly where its law
     * says of the arguments, read as {@code ofTheArguments}.
     */
    record ByALaw(ValueName.Stdlib operation, AnswerAspect aspect, Derivation ofTheArguments)
            implements Derivation {

        public ByALaw {
            Objects.requireNonNull(operation, "a law is of an operation");
            Objects.requireNonNull(aspect, "a law is about one side of what it answers");
            Objects.requireNonNull(ofTheArguments, "and comes to something of its arguments");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(ofTheArguments);
        }
    }

    /** A law that says the same thing whatever the arguments are. */
    record ALawSettles(boolean holds) implements Derivation {

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds);
        }
    }

    /** A law that states every one of {@code parts}, or at least one where not {@code every}. */
    record ALawJoins(List<Derivation> parts, boolean every) implements Derivation {

        public ALawJoins {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a law joins two statements or more");
            }
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            List<Proposition> each = new ArrayList<>(parts.size());
            parts.forEach(part -> each.add(numbering.of(part)));
            return every ? Proposition.all(each) : Proposition.any(each);
        }
    }

    /**
     * A law that states a value comes out on the side {@code observed} was read as holding, or on
     * the other one where not {@code holds}.
     */
    record OnTheSideALawNames(Derivation observed, boolean holds) implements Derivation {

        public OnTheSideALawNames {
            Objects.requireNonNull(observed, "a side is of something read");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            Proposition read = numbering.of(observed);
            return holds ? read : read.denied();
        }
    }

    /** A law that states two subjects are one value, or not where not {@code holds}. */
    record TheSameValue(DecisionSubject one, DecisionSubject other, boolean holds)
            implements Derivation {

        public TheSameValue {
            Objects.requireNonNull(one, "a sameness is of two subjects");
            Objects.requireNonNull(other, "a sameness is of two subjects");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.SameValue(one, other, holds);
        }
    }


    /**
     * The number an operation answering the order of its two arguments answered, compared with a
     * number that settles which side of nought it falls on: the comparison of the two arguments
     * that sign stands for.
     */
    record AnOrderOfItsArguments(ValueName.Stdlib operation, Derivation ofTheArguments)
            implements Derivation {

        public AnOrderOfItsArguments {
            Objects.requireNonNull(operation, "a law is of an operation");
            Objects.requireNonNull(ofTheArguments, "an order is of the arguments");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return numbering.of(ofTheArguments);
        }
    }

    /**
     * The number an operation answering the order of its two arguments answered, compared with a
     * number every answer the library says it can give comes out {@code holds} against.
     */
    record ASignItsBoundsSettle(ValueName.Stdlib operation, boolean holds) implements Derivation {

        public ASignItsBoundsSettle {
            Objects.requireNonNull(operation, "a law is of an operation");
        }

        @Override
        public Proposition conclusion(Conclusion numbering) {
            return new Proposition.Always(holds);
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
