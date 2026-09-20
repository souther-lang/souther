package souther.compiler.partition;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.observe.RowRef;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * What tells one thing a row is owed for from every other, over the derivations that state such
 * things.
 *
 * <p>Closed, so that a surface writing one writes every shape there is: a derivation added arrives
 * at each of them as a case to decide about rather than as a value that falls through. What the
 * shapes have in common is what they are for and not what they hold — a line's point is a point of
 * an authored line at a level, an arm's is the fork and which of its ways, a class's is the axis and
 * which class of it, a decision rule's is what the path consulted — so there is nothing here to lift
 * out of them.
 *
 * <p><b>Not a handle a search steers by.</b> What a proposal targets is one of these; how a search
 * reaches it is the search's own — {@link Generator.ArmOwed} names an occurrence a run is recorded
 * at, and what a requirement search came back standing at is values. Held as one value, a proposal
 * merged with another because their stimuli agreed would lose which obligations it was for, and the
 * account would be keyed on whatever the search happened to name.
 *
 * <p>Below the account rather than in it. The generator, the readings and the account all join on
 * this, and the two of them that cannot see the account would each have had a vocabulary of their
 * own — which is the parallel bookkeeping this is here to have none of.
 */
public sealed interface ObligationIdentity
        permits ObligationIdentity.OfALine, ObligationIdentity.OfABorder, ObligationIdentity.OfAnArm,
                ObligationIdentity.OfARow, ObligationIdentity.OfAnOutputCase,
                ObligationIdentity.OfADecisionRule,
                ObligationIdentity.OfACombinationOfDecisions,
                ObligationIdentity.OfAFallbackPairCell, WhereACaseOfAnInputIsOwed {

    /** A point of a line, which is what the border accounts are owed at. */
    record OfALine(BorderObligationPoint point) implements ObligationIdentity {

        public OfALine {
            Objects.requireNonNull(point, "an obligation is told apart by something");
        }
    }

    /**
     * A whole line, which is what the lines beside it are asked of.
     *
     * <p>Beside {@link OfALine} and one grain coarser. That one is a place on a line and there are
     * four of them; this is the line itself, because what a row shows here is which of two lines the
     * model draws and a line is what two lines are two of. Keyed on a point, the same question would
     * be owed four times over and a row answering it would leave three of them open.
     *
     * <p>The line a debt is owed at and not the reading that met it, for the reason a point's is:
     * one authored line read at several positions is one row to write.
     */
    record OfABorder(BorderObligationId line) implements ObligationIdentity {

        public OfABorder {
            Objects.requireNonNull(line, "an obligation is told apart by something");
        }
    }

    /**
     * An arm of a body, which is what the arm account is owed at.
     *
     * <p>The obligation and not an occurrence of it. A non-recursive helper is spliced into each
     * body that calls it, so one arm the author wrote stands in the running tree several times;
     * covering it through a second call site establishes nothing the first did not.
     */
    record OfAnArm(CoverageSites.Obligation arm) implements ObligationIdentity {

        public OfAnArm {
            Objects.requireNonNull(arm, "an obligation is told apart by something");
        }
    }

    /**
     * A row an author wrote, which is what the row account is owed an answer at.
     *
     * <p>Not an arm a row stands at. An arm is owed a row and the account of arms says whether one
     * goes through it; a row is owed an answer and is owed it whether or not the behavior branches
     * at all. One {@code <?>} row through one arm is two things to do, told apart here by being
     * keyed on two different shapes.
     *
     * <p>{@link RowRef} and not {@link souther.compiler.observe.RowIdentity}. A row written with no
     * name is numbered within the source that writes it, so a behavior exampled in a module and in
     * an attached file has a first row in each — and an account keyed on what the row names itself
     * would hold one entry for two rows an author has to go and look at separately.
     */
    record OfARow(RowRef rowRef) implements ObligationIdentity {

        public OfARow {
            Objects.requireNonNull(rowRef, "an obligation is told apart by something");
        }
    }

    /** A class of a position, which is what the domain account is owed at. */
    record OfAClass(ClassOfAPosition classOfAPosition) implements WhereACaseOfAnInputIsOwed {

        public OfAClass {
            Objects.requireNonNull(classOfAPosition, "an obligation is told apart by something");
        }
    }

    /**
     * A case of an input, where nothing divides that input into classes.
     *
     * <p>Beside {@link OfAClass} and not instead of it. A case of a sum an input ranges over and
     * the class that sum makes of the position are one thing a row is owed for — where both
     * derivations are about one behavior's own position. A behavior with no input of its own has
     * the first and not the second: its stages are where its input is read, and each of them is a
     * behavior with positions of its own. Keyed on a stage's axis, this behavior's finding would
     * borrow that behavior's account entry, which is a reader rebuilding an identity somewhere
     * other than where the obligation is.
     *
     * <p>So what tells one of these from another is the behavior, which of its inputs, and which
     * case — the input by its number, because a behavior that declares no parameters has no name to
     * call it by and borrowing a stage's parameter name is the same borrowing said in words.
     *
     * @param at which input of the signature, in the order the signature takes them
     */
    record OfAnInputCase(String behavior, int at, TypeSymbol caseOfTheInput)
            implements WhereACaseOfAnInputIsOwed {

        public OfAnInputCase {
            Objects.requireNonNull(behavior, "a case of an input is some behavior's");
            Objects.requireNonNull(caseOfTheInput, "an obligation is told apart by something");
            if (at < 0) {
                throw new IllegalArgumentException(
                        "a case of an input is at one of the inputs: " + at);
            }
        }
    }

    /**
     * A case of the output, which is what the signature's output account is owed at.
     *
     * <p>The behavior and which case, and nothing about a position. An output has none — an axis is
     * of an input — so no other account can hold this and there is no second entry for it to
     * coincide with, which is what makes the array beside the output cases the one place it is.
     *
     * <p>The behavior beside the case for the reason a rule of a decision has one: two behaviors
     * answering with the same sum owe that case separately, and an identity that left the behavior
     * out would have one of them discharged by the other's row.
     */
    record OfAnOutputCase(String behavior, TypeSymbol caseOfTheOutput)
            implements ObligationIdentity {

        public OfAnOutputCase {
            Objects.requireNonNull(behavior, "a case of an output is some behavior's");
            Objects.requireNonNull(caseOfTheOutput, "an obligation is told apart by something");
        }
    }

    /**
     * A rule of the decision a body states, which is what the decision account is owed at.
     *
     * <p>The behavior beside the rule. A rule is told apart by the distinctions it consulted, and
     * those are written in the terms of a body's own positions — so two behaviors comparing
     * same-named positions the same way state equal rules, and an identity that left the behavior
     * out would have one of them discharged by the other's row.
     */
    record OfADecisionRule(String behavior, DecisionRule rule) implements ObligationIdentity {

        public OfADecisionRule {
            Objects.requireNonNull(behavior, "a rule of a decision is some body's");
            Objects.requireNonNull(rule, "an obligation is told apart by something");
        }
    }

    /**
     * One combination of the decisions a body settles a value by: the way in to where they meet,
     * and one outcome of each of them at it.
     *
     * <p>Told apart by what a row has to have been seen doing, in the words the model states it in.
     * A {@link souther.compiler.reading.Condition} is the reading's own half of a decision — which position, which way it
     * came out, at which occurrence — and the claim beside it is where a run of this compilation is
     * recorded doing it. Held on the claims, one requirement would be renamed by the body being
     * instrumented differently; held on the group, a factor gaining an outcome would rename the
     * combinations that have nothing to do with it.
     *
     * <p>A set, and so two ways of arriving at the same decisions are one thing to ask for. What
     * divides them between the way in and the outcomes is how the walk found them, which is not
     * something a row can do differently.
     *
     * <p>The classes are no part of it. Which classes of a position a combination leaves open is
     * how a search steers a candidate towards it, and a row that was seen making the decisions
     * settles this however that reading came out.
     */
    record OfACombinationOfDecisions(String behavior, Set<souther.compiler.reading.Condition> settled)
            implements ObligationIdentity {

        public OfACombinationOfDecisions {
            Objects.requireNonNull(behavior, "a combination of decisions is some body's");
            settled = Set.copyOf(settled);
            if (settled.isEmpty()) {
                // A combination of a body's decisions is decisions being settled. Empty, it would
                // be a requirement every run meets by having run at all.
                throw new IllegalArgumentException(
                        "a combination of decisions is some decisions coming out some way");
            }
        }
    }

    /**
     * One combination of two classes, where the body's decisions meet nowhere and the pair space is
     * the criterion.
     *
     * <p>Beside {@link OfACombinationOfDecisions} and not under it. What settles the one is a run
     * seen making the decisions; what settles this is where the values classify, because there is
     * no meeting for a run to have reached — a behavior whose decisions never come together, and an
     * injected behavior, which has no body to read at all. Held as one shape, a reader would have
     * to ask which kind it had before it knew what evidence to look for.
     *
     * <p>The two classes, unordered. A combination is between two positions and neither of them is
     * the first one. A reader that has to walk them, or word them, takes them from
     * {@link #inOrder}.
     */
    record OfAFallbackPairCell(String behavior, Set<ClassOfAPosition> classes)
            implements ObligationIdentity {

        public OfAFallbackPairCell {
            Objects.requireNonNull(behavior, "a combination of two classes is some behavior's");
            classes = Set.copyOf(classes);
            if (classes.size() != 2) {
                throw new IllegalArgumentException(
                        "a combination of two classes is of two of them: " + classes);
            }
            if (classes.stream().map(ClassOfAPosition::at).distinct().count() != 2) {
                // Two classes of one position are not a combination: no value holds both, so the
                // requirement is one nothing could ever meet.
                throw new IllegalArgumentException(
                        "a combination is between two positions: " + classes);
            }
        }

        /** The two classes in the one order classes are named in. */
        public List<ClassOfAPosition> inOrder() {
            return classes.stream().sorted().toList();
        }
    }
}
