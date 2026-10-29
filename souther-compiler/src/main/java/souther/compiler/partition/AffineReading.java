package souther.compiler.partition;

import souther.compiler.abort.AbortKind;
import souther.compiler.check.AffineForms;
import souther.compiler.check.Choice;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.ValueStanding;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Location;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.inputs.DecimalOperation;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TotalsOfOneRun;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Predicate;

/**
 * A comparison read as one statement: {@code Σ coef·position REL threshold}.
 *
 * <p><b>What a rule says, and not how it was written.</b> {@code a + 1 <= 10}, {@code 2 * a <= 10}
 * and {@code a <= b - 1} were each a comparison the measure could not read, because the readers
 * before this one wanted a bare position on one side and a written value or a bare position on the
 * other. What decides which quantity a rule cuts is this form and never the spelling, so
 * {@code a > b}, {@code a + 0 > b} and {@code a > b + 0} are one rule about one quantity.
 *
 * <p>The constant is moved to the threshold rather than kept in the quantity. {@code a + 1 <= 10} is
 * {@code a <= 9} and {@code 2 * a <= 9} is {@code 2 * a <= 9}, so a quantity is constant-free and a
 * threshold is a number. Left in the quantity, the values {@code 2 * a} takes would be the even
 * numbers under one spelling and the odd ones shifted by nine under another, and the two would
 * disagree about where the border's points are.
 *
 * <p>The arithmetic is {@link AffineForms}'s, which is the walk the discharge check reads a clause
 * with. The atoms are this side's: a position of a behavior's input, or a count taken of one.
 *
 * @param form  the quantity, with no constant in it
 * @param cut   where the rule cuts it
 * @param claim what the operator states about the threshold's own value
 */
record AffineReading(LinearForm<NumericTerm> form, ExactRatio cut, ComparisonClaim claim) {

    /**
     * What reading {@code comparison} as a line came to.
     *
     * <p>Three answers, because two of them used to be one absence. A reading that stopped and a
     * reading that went all the way and found no quantity are opposite facts: the first says this
     * compiler fell short, and the second says the rule cuts nothing — {@code a - a > 0} is read
     * perfectly and divides no position. Told apart only by a {@code null}, whoever asked had to
     * guess, and guessed that a rule it had read in full was written in a form it could not read.
     */
    sealed interface OfAComparison {

        /**
         * What reading the comparison told of the operations a row of its lines gets past: what
         * the walk collected where it read a line, and no claim where it did not. A comparison
         * that was not read as a sum the walk composed says nothing of what the program works
         * out, which is not that the program adds the form up.
         *
         * <p>The one exception is a reading that stopped, whatever it stopped at: the lines drawn
         * from it are another analysis's (a product, a remainder, a date, a fold, a lookup, the
         * arms of a branch), built from the statement's form and not from this walk. The
         * expression it stopped at is that analysis's own, and what the program works out beside
         * that expression is read again with the stopped value held aside ({@link Stopped#apart}).
         * Where nothing beside it can stop a row the lines are answered for their rows by the
         * form's sizes ({@link UndividedByARelation.Working#NOTHING}); where an operation beside it
         * can, the operations told are kept and the rest is not told.
         */
        static UndividedByARelation.Working workingOf(OfAComparison read) {
            return switch (read) {
                case Cuts cuts -> cuts.working();
                case Stopped stopped -> stopped.apart(_ -> false);
                case CutsNothing _, NotHeld _ -> UndividedByARelation.Working.UNREAD;
            };
        }

        /**
         * The line the comparison draws.
         *
         * @param mirrored whether the form is the right side less the left rather than the left
         *                 less the right, which is how the line is faced to the position the left
         *                 names first ({@link #facesTheOtherWay}) and is what tells which of the two
         *                 written sides is above on either side of the line
         * @param working  the sums, differences, products and negations of whole numbers the
         *                 comparison works out as it is written, each over the numbers it was
         *                 read through, and whether they are all a run can stop at: what the
         *                 line is cut as does not say which of them the program runs, and these do
         */
        record Cuts(AffineReading read, boolean mirrored, UndividedByARelation.Working working)
                implements OfAComparison {

            public Cuts {
                Objects.requireNonNull(read, "a comparison that cuts has a line");
                Objects.requireNonNull(working, "a comparison says what it works out");
            }
        }

        /**
         * Read to the end, and the quantity it cuts is nothing: a comparison of constants, or one
         * whose positions cancel. Nothing is missing here.
         *
         * <p>{@code read} is every number of the input this reading named on the way, whether or not
         * it survived the cancellation. What the rule is about is not what is left of it: {@code a -
         * a <= 0} states something about {@code a} and holds of every row, and a reader told only
         * that the quantity is empty would have to go back to the operands to find out where to say
         * so — which is a second account of what the rule names, beside the reading that has just
         * read it. A comparison of constants named nothing and comes back with nothing.
         *
         * <p>A set, because naming one number twice is naming it once. Which order a document lists
         * them in is not carried here and is not the order they were met in: that is how the rule
         * was spelled, and it is settled where the coordinates are made
         * ({@link AffineReading#filedAt}).
         *
         * <p>{@code difference} is what the left side exceeds the right by, which is the same for
         * every row — so which way the comparison comes out is settled by it and the relation, and
         * a reader asking that is not sent back to the operands to fold them a second way.
         */
        record CutsNothing(java.util.Set<NumericTerm> read, ExactRatio difference)
                implements OfAComparison {

            public CutsNothing {
                read = java.util.Set.copyOf(read);
                Objects.requireNonNull(difference,
                        "a comparison that cuts nothing still has its two sides' difference");
            }

            /** Whether a comparison stating {@code rel} of its left side against its right comes
             *  out holding, which is the same for every row. */
            boolean holds(Rel rel) {
                return rel.holds(difference.signum());
            }
        }

        /**
         * Read to the end, each side as a form, and the difference of the two has no representation.
         *
         * <p>Its own answer beside {@link CutsNothing} and {@link Stopped}. Nothing cancelled, so
         * the quantity is not empty; the reading did not stop on an expression it could not read,
         * so the rule is a form it reads.
         * What is missing is a number to say what the difference is, and a reader told either of the
         * others would be told something about the rule that is not so. A rule the model wrote in
         * good faith — a coefficient at one end of the range weighed against one at the other —
         * arrives here.
         *
         * <p>{@code read} is every number of the input this reading named on the way, for the same
         * reason {@link CutsNothing} carries it.
         */
        record NotHeld(Set<NumericTerm> read) implements OfAComparison {

            public NotHeld {
                read = Set.copyOf(read);
            }
        }

        /**
         * The reading stopped: where, in what environment, and for the reason the arithmetic gave.
         * The reason is the arithmetic's own, so a reader of this takes it as it is.
         */
        record Stopped(AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> failure,
                        WhatLiesBesideTheStop beside) implements OfAComparison {

            public Stopped {
                java.util.Objects.requireNonNull(failure, "a reading that stopped stopped somewhere");
                Objects.requireNonNull(beside, "what the comparison works out beside the stop");
            }

            /**
             * What the program works out beside the expression the reading stopped at, for a
             * relation drawn by an analysis that owns that expression: none of the stopped value's
             * own operations are told, and a row is not shown computed for an operation beside it
             * that is not. {@code answersFor} says which other expressions nothing here reads the
             * analysis answers for as well; any other that may end a run leaves the operations
             * told as not every one.
             */
            UndividedByARelation.Working apart(Predicate<Core> answersFor) {
                return beside.apart(answersFor);
            }

            /**
             * The same, for the analysis of a quotient by a value, whose lines are drawn on the
             * dividend and the divisor with the divisor away from nought, and which answers for
             * everything written under the quotient. The dividend and the divisor are worked out
             * on every row of those lines, and the quotient of two numbers answers on every divisor
             * but nought, so they are told with the rest. Not every operation is told where the
             * quotient is not of that kind.
             */
            UndividedByARelation.Working ofTheQuotientAwayFromNought(Core division) {
                return beside.ofTheQuotientAwayFromNought(division);
            }

            /** The expression the reading stopped at. */
            public Core node() {
                return failure.node();
            }

            /** The environment it was being read in. */
            public InputReads at() {
                return failure.at();
            }
        }
    }

    /**
     * One expression as a form of the input's numbers, or null where the arithmetic stops on it.
     *
     * <p>The reading a side of a comparison gets ({@link #read}), asked of a part of one: a
     * dividend is read as a side is, so the same expression is the same form wherever it stands.
     */
    static LinearForm<NumericTerm> formOf(Core expression, InputReads reads, InputReading read) {
        AffineForms.Outcome<NumericTerm, InputReads> outcome = AffineForms.outcome(expression,
                reads, reading(read, new LinkedHashSet<>(), new ElementsMet(),
                        new WhatWasTold()));
        return outcome instanceof AffineForms.Outcome.Composed<NumericTerm, InputReads> composed
                ? composed.form() : null;
    }

    /**
     * The same, of the input {@code ofTheInput} reads, with the names as {@code reads} has them, saying
     * which of the four it is.
     */
    static OfAComparison read(StatedComparison comparison, InputReads reads,
                              InputReading ofTheInput) {
        InputDomain inputs = ofTheInput.domain();
        RuleReadingSource ruleSource = ofTheInput.rules();
        // What this reading names as it goes, kept so that a reading which ran to the end can say
        // what it was about without anybody reading the comparison again.
        java.util.Set<NumericTerm> named = new java.util.LinkedHashSet<>();
        // One element of each container for the whole comparison, whichever side names it.
        ElementsMet met = new ElementsMet();
        // What the two sides work out, as they are written.
        WhatWasTold told = new WhatWasTold();
        // The left first where both stop, which is the side a threshold would be read off.
        LinearForm<NumericTerm> left = null;
        for (Core side : java.util.List.of(comparison.left(), comparison.right())) {
            AffineForms.Outcome<NumericTerm, InputReads> read =
                    AffineForms.outcome(side, reads,
                            reading(ofTheInput, named, met, told));
            if (read instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> stopped) {
                return new OfAComparison.Stopped(stopped,
                        new WhatLiesBesideTheStop(comparison, reads, ofTheInput, stopped.node()));
            }
            if (left == null) {
                left = ((AffineForms.Outcome.Composed<NumericTerm, InputReads>) read).form();
            } else {
                // Each side was read as a form, and the difference of the two is what the rule is
                // about. Two forms held one by one can have a difference no ratio holds — a
                // coefficient at one end of the exponents against one at the other — and that is a
                // reading that ran to the end and could not write down what it found, which is
                // neither a rule with no line nor a form the arithmetic did not read.
                if (!(left.minus(
                        ((AffineForms.Outcome.Composed<NumericTerm, InputReads>) read).form())
                        instanceof ExactAnswer.Held<LinearForm<NumericTerm>> difference)) {
                    return new OfAComparison.NotHeld(named);
                }
                LinearForm<NumericTerm> whole =
                        TotalsOfOneRun.addedUp(difference.value(), inputs, ruleSource);
                if (whole.coefs().isEmpty()) {
                    return new OfAComparison.CutsNothing(named, whole.constant());
                }
                AffineReading here = new AffineReading(
                        new LinearForm<>(ExactRatio.ZERO, whole.coefs()),
                        whole.constant().negated(), comparison.claim());
                // Turned round here and nowhere else. `48 >= 3a + 6b` and `3a + 6b <= 48` are one
                // rule, and a reader that met the first without turning it round drew its border on
                // `-3a - 6b` — the same four points under a name no author wrote, and a different
                // line from the rule written the other way.
                boolean mirrored =
                        here.facesTheOtherWay(subjectOf(comparison.left(), left, reads, ruleSource));
                return new OfAComparison.Cuts(mirrored ? here.mirrored() : here, mirrored,
                        told.working());
            }
        }
        throw new IllegalStateException("a comparison has two sides");
    }

    /**
     * The line {@code form stated 0} draws, where {@code form} is over the input's numbers alone.
     *
     * <p>What a comparison states is read once ({@link Pullback#ofAComparison}), and this is that
     * statement put on the input space: the constant moved to the threshold, and the form faced the
     * way the comparison's left side names ({@link #facesTheOtherWay}). The facing is how the line is
     * named in a report and not what it is: the two ways are one statement.
     *
     * @param leftSide the comparison's left side as written, which is only asked which position it
     *                 names first
     */
    static AffineReading stating(LinearForm<NumericTerm> written, Rel stated, Core leftSide,
                                 InputReads reads, InputReading read) {
        RuleReadingSource ruleSource = read.rules();
        LinearForm<NumericTerm> form = TotalsOfOneRun.addedUp(written, read.domain(), ruleSource);
        AffineReading here = new AffineReading(new LinearForm<>(ExactRatio.ZERO, form.coefs()),
                form.constant().negated(), ComparisonClaim.stating(stated));
        return here.facesTheOtherWay(subjectOf(leftSide, form, reads, ruleSource))
                ? here.mirrored() : here;
    }

    /**
     * The order a form's positions are named in, which settles what "the first coefficient" means.
     *
     * <p>By the position's own name, because that is the one thing about a form that does not depend
     * on how it was written. A form is a map; the order its coefficients were recorded in is the
     * order the author happened to add them in, and a report is a document compared against the one
     * written last time.
     */
    static java.util.List<Map.Entry<NumericTerm, ExactRatio>> ordered(
            LinearForm<NumericTerm> form) {
        return NumericTerms.entriesInOrder(form.coefs());
    }

    /**
     * Where a reading that reached the numbers files what it found, in the order a document names
     * them.
     *
     * <p><b>The numbers and not the places they sit at.</b> A reader that got as far as the terms
     * has the operation each number is taken by, and two operations over one path are two rules a
     * report has to tell apart ({@link souther.compiler.inputs.FilingCoordinate}); the coordinate
     * that names only the place is for a reader that did not get that far. Written out again at a
     * second reader, the weaker of the two is the one that would be reached for, since a path is
     * what every term can be asked for.
     *
     * <p>By the term's own name, for the reason {@link #ordered} gives: how a rule was spelled is
     * not what a document is keyed on, and a report is compared against the one written last time.
     * So the order the reading happened to meet them in is not carried, and neither is a set's.
     */
    static java.util.List<souther.compiler.inputs.FilingCoordinate> filedAt(
            java.util.Collection<NumericTerm> terms) {
        return souther.compiler.inputs.NumericTerms.inOrder(terms).stream()
                .<souther.compiler.inputs.FilingCoordinate>map(
                        souther.compiler.inputs.FilingCoordinate::of)
                .distinct().toList();
    }

    /**
     * What this reader answers about its own environment, which is what tells its atoms from
     * another reader's.
     *
     * <p>{@code named} takes every number this names, which is the one place a node of the tree
     * becomes a term of the input. Collected here rather than recovered afterwards: what a rule is
     * about is what the reading of it named, and a reader working that out again from the operands
     * is a second account of it.
     *
     * <p>{@code inputs} is held here and not threaded through the walk. What the environment
     * answers changes at every binding the walk goes under; the reading of the input is one value
     * for the whole reading of one comparison, and this reader lives exactly that long.
     */
    private static AffineForms.Reading<NumericTerm, InputReads> reading(
            InputReading ofTheInput, Set<NumericTerm> named, ElementsMet met, WhatWasTold told) {
        return reading(ofTheInput, named, met, told, null);
    }

    /**
     * The same, holding aside the value of {@code stoppedAt} where it is not null: the expression a
     * reading stopped at stands for an atom no operation is told over, so that the rest of the
     * comparison is read for what it works out.
     */
    private static AffineForms.Reading<NumericTerm, InputReads> reading(
            InputReading ofTheInput, Set<NumericTerm> named, ElementsMet met, WhatWasTold told,
            StoppedValues stoppedAt) {
        InputDomain inputs = ofTheInput.domain();
        RuleReadingSource ruleSource = ofTheInput.rules();
        ReadMeaning.WhereKept kept = KeptTruths.readIn(ofTheInput);
        return new AffineForms.Reading<NumericTerm, InputReads>() {

            /**
             * An operation of whole numbers the walk composed, told with the number it comes to:
             * where its type says it answers only between two ends, a row is computed only where
             * that number lies between them. An operation whose type says a run may stop at it
             * and not where is not every operation, and what is told is then not all there is.
             *
             * <p>An operation over the stopped value is not told: the number it comes to is not
             * the form's, and a row held to the form's would be refused for an operation that
             * does not stop it. What the reading then says of every operation is that it stops
             * no row or stops one only where the owner of the value answers for it, or the
             * operations told are not every one.
             */
            @Override
            public void composed(Core operation, LinearForm<NumericTerm> form,
                                 List<LinearForm<NumericTerm>> operands) {
                WhereAnOperatorAnswers where = switch (Core.withoutStanding(operation)) {
                    case Core.Binary binary -> WhereAnOperatorAnswers.ofAnOperator(binary.op(),
                            binary.type(), List.of(binary.left().type(), binary.right().type()));
                    case Core.Neg neg -> WhereAnOperatorAnswers.ofANegation(neg.type());
                    default -> null;
                };
                List<StoppedValues.Held> over = stoppedAt == null ? List.of()
                        : stoppedAt.heldIn(form);
                if (!over.isEmpty()) {
                    if (!stopsNoRowOrIsTheOwners(where, form, over)) {
                        told.exact = false;
                    }
                    return;
                }
                if (where instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held) {
                    // One no row of the places it is over stops at is not an operation a run can
                    // stop at, and there is nothing to tell of it.
                    FormRange range = FormRange.of(form, ofTheInput);
                    UndividedByARelation.IntOperation operationTold =
                            new UndividedByARelation.IntOperation(form, held.least(),
                                    held.greatest(), told.workedOutOf(operation));
                    if ((range == null || !range.liesWithin(held.least(), held.greatest()))
                            && !told.operations.contains(operationTold)) {
                        told.add(operation, operationTold);
                    }
                } else if (!(where instanceof WhereAnOperatorAnswers.Everywhere)
                        // A decimal operation has no region; a row is asked by working it out.
                        && !(where instanceof WhereAnOperatorAnswers.NotStated
                                && told.addsDecimal(operation, form, operands))) {
                    told.exact = false;
                }
            }

            /**
             * A node read without telling of every operation it works out. One written around the
             * expression the reading stopped at is the analysis that owns the expression's to
             * answer for, as the expression is.
             */
            @Override
            public void unobserved(Core node) {
                told.exact = false;
            }

            @Override
            public boolean readsATotalOfWhatIsWrittenOut() {
                return true;
            }

            /**
             * A total over a list written out, told as the one operation it is: the library adds
             * the numbers up exactly and holds only the total to the type, so a run stops at the
             * call where the total passes the ends an {@code Int} sum has, and at no partial sum.
             * It is worked out after the operations of the elements it adds.
             */
            @Override
            public void totalled(Core call, LinearForm<NumericTerm> total,
                                 List<Core> elements) {
                if (WhereAnOperatorAnswers.ofAnOperator(BinOp.ADD, Type.INT,
                        List.of(Type.INT, Type.INT))
                        instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held) {
                    told.add(call, new UndividedByARelation.IntOperation(total, held.least(),
                            held.greatest(), told.workedOutOf(elements)));
                } else {
                    told.exact = false;
                }
            }

            /**
             * Whether {@code node}, an expression nothing here reads other than the stopped one,
             * ends no run, or is one the analysis that drew the lines answers for. Any other that
             * may end a run has no owner here.
             */
            private boolean worksOutNothingBesideTheStop(Core node) {
                return WhatARunMayEndFor.endsNoneBeneath(node) || stoppedAt.answersFor(node);
            }

            /**
             * Whether {@code form}, an operation over the expressions {@code over} held aside and
             * worked out as {@code where} says, stops no row: it answers everywhere, or the
             * numbers it comes to lie where it answers, from the numbers each expression held
             * aside is known to come to (none, for one nothing is known of). Or stops one only
             * where the analysis that owns the stopped value answers for it, which is a sum of the
             * addends of the comparison over that value and no other held aside, asked once the
             * comparison has been read ({@link WhatLiesBesideTheStop#beside}). Anything else
             * worked out over them is no owner's.
             */
            private boolean stopsNoRowOrIsTheOwners(WhereAnOperatorAnswers where,
                                                    LinearForm<NumericTerm> form,
                                                    List<StoppedValues.Held> over) {
                if (where instanceof WhereAnOperatorAnswers.Everywhere) {
                    return true;
                }
                if (!(where instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held)) {
                    return false;
                }
                FormRange range = FormRange.of(form, stoppedAt.read(), stoppedAt.ranges());
                if (range != null && range.liesWithin(held.least(), held.greatest())) {
                    return true;
                }
                if (over.size() == 1 && stoppedAt.isAPlainStop(over.get(0))) {
                    told.sumsOverTheStop.add(form);
                    return true;
                }
                return false;
            }

            @Override
            public boolean makingEndsNoRun(Core.Construct construct) {
                return ClausesInOrder.at(construct, ruleSource).governsNothing();
            }

            @Override
            public Symbols symbols() {
                return ruleSource.symbols();
            }

            @Override
            public DeclarationAccess declarations() {
                return ruleSource.declarations();
            }

            @Override
            public LinearForm<NumericTerm> leafOf(Core node, InputReads at) {
                LinearForm<NumericTerm> numbers =
                        InputNumber.formOf(node, inputs, at, ruleSource, met);
                if (numbers != null) {
                    named.addAll(numbers.coefs().keySet());
                    // A number worked out by a run that may stop, and no operation here tells
                    // where. What may stop one is its owners' to say, and a node they do not say
                    // of is one that may.
                    if (!stopsOnlyWhereItsAnswerHasNoPlace(node)) {
                        told.exact = false;
                    }
                    if (isAPlainRead(node)) {
                        told.readsTheInput(numbers);
                    }
                    return numbers;
                }
                if (stoppedAt == null) {
                    return null;
                }
                // Each expression nothing here reads is held aside as an atom of its own. What the
                // one the reading stopped at works out is its owner's to show; any other has no
                // owner here unless it ends no run or the analysis that drew the lines says so,
                // and the operations are then not every one.
                StoppedValues.Held aside = stoppedAt.holdAside(node);
                if (aside.firstMeeting()) {
                    if (!aside.theStop) {
                        if (!worksOutNothingBesideTheStop(node)) {
                            told.exact = false;
                        }
                    } else if (stoppedAt.quotientAwayFromNought()) {
                        operandsOfTheQuotient(node, at);
                    }
                    if (aside.aChoice) {
                        aside.rangeIs(rangeOfTheArms(node, at));
                    }
                }
                return LinearForm.atom(aside.atom);
            }

            /**
             * The numbers the arms of the choice {@code node} answer between them, or null where
             * an arm is no form of places with ends.
             */
            private FormRange rangeOfTheArms(Core node, InputReads at) {
                FormRange hull = null;
                // Read apart: what an arm works out is not told of the comparison being read.
                AffineForms.Reading<NumericTerm, InputReads> apart = reading(stoppedAt.read(),
                        new LinkedHashSet<>(), new ElementsMet(), new WhatWasTold());
                for (Choice.Arm arm : Choice.of(Core.withoutStanding(node)).arms()) {
                    if (!(AffineForms.outcome(arm.answers(), at, apart)
                            instanceof AffineForms.Outcome.Composed<NumericTerm, InputReads> answer)) {
                        return null;
                    }
                    FormRange range = FormRange.of(answer.form(), stoppedAt.read());
                    if (range == null) {
                        return null;
                    }
                    hull = hull == null ? range : hull.hull(range);
                }
                return hull;
            }

            /**
             * What a quotient by a value works out of its own: its dividend and its divisor, each
             * read as any side is. The quotient is a number wherever its divisor is not nought,
             * which the analysis that owns it keeps its rows to; any other operation at the stop
             * is not told.
             */
            private void operandsOfTheQuotient(Core node, InputReads at) {
                if (!(Core.withoutStanding(node) instanceof Core.Binary quotient)
                        || quotient.op() != BinOp.DIV
                        || !(WhereAnOperatorAnswers.ofAnOperator(quotient.op(), quotient.type(),
                                List.of(quotient.left().type(), quotient.right().type()))
                                instanceof WhereAnOperatorAnswers.WhereTheDivisorIsNotNought)) {
                    told.exact = false;
                    return;
                }
                for (Core operand : List.of(quotient.left(), quotient.right())) {
                    if (AffineForms.outcome(operand, at, this)
                            instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads>) {
                        told.exact = false;
                    }
                }
            }

            @Override
            public InputReads inside(Core.LetIn li, InputReads at) {
                return at.and(li.binder(), li.value());
            }

            /**
             * A name given arithmetic over positions, which is the arithmetic the rule cuts.
             *
             * <p>Only where the name is nothing of its own. A name that is a position is that
             * position and the leaf answers with it; a name an operation handed an element on
             * stands for one element of what the operation answered, and the expression behind it
             * was written about every element rather than about the value at this read — put where
             * the name stands, it would draw a line at a position whose values are not the ones the
             * rule is about. Which of those a name is, is one answer from one place
             * ({@link InputReads#meaningOf}), read here rather than worked out again.
             */
            @Override
            public ValueStanding.ReadThrough<InputReads> readThrough(Core.Read read, InputReads at) {
                return NameAnswers.denoting(read, at, ruleSource.symbols(),
                        ruleSource.newtypes());
            }

            /**
             * A name an operation handed an element on, where the container was written out. Read
             * for the count the one answer comes back with, beside the walk that says which
             * positions a rule is about, so the two meet a plurality with the same knowledge.
             */
            @Override
            public java.util.List<ValueStanding.ReadThrough<InputReads>> alternativesOf(
                    Core.Read read, InputReads at) {
                return NameAnswers.alternativesOf(read, at, ruleSource.symbols(),
                        ruleSource.newtypes(), kept);
            }

            @Override
            public ValueStanding.ReadThrough<InputReads> taken(Core node, InputReads at) {
                return NameAnswers.taken(node, at);
            }

            @Override
            public LinearForm<Core> takenAsAForm(Core node, InputReads at) {
                return NameAnswers.takenAsAForm(node, at);
            }

            @Override
            public boolean readsThrough(Core.FieldAccess fa, InputReads at) {
                // Read through where the target is at no position of the input: a field of a value
                // that stands nowhere is arithmetic's to walk into, since it is no place a row
                // writes at.
                boolean stands = switch (at.pathOf(fa.target(), ruleSource.newtypes())) {
                    case PathResolution.At _ -> true;
                    case PathResolution.NotAPosition _ -> false;
                    // A target that may stand at a position of the input does, on some run, and
                    // which is not for arithmetic to decide by walking into it. Read through, a
                    // field of it would be a term over a place it may never stand at.
                    case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> true;
                };
                return !stands
                        && !Location.isStep(fa.target().type(), fa.field(), ruleSource.newtypes());
            }
        };
    }

    /**
     * Whether working {@code node} out ends a run only where its own answer has no place in its
     * type, and nothing under it ends one: an operation refuses only what its own answer has no
     * place for. A number that is the value of such a node is a value of its type, and a row
     * standing at it is not stopped by working the node out; what is under it that ends a run is
     * not the number's, and is not told.
     */
    private static boolean stopsOnlyWhereItsAnswerHasNoPlace(Core node) {
        if (!(WhatARunMayEndFor.itself(node) instanceof WhatARunMayEndFor.Endings.Known own)
                || !own.kinds().kinds().stream()
                .allMatch(kind -> kind == AbortKind.REQUIRED_FORM_HAS_NO_PLACE)) {
            return false;
        }
        boolean[] under = {true};
        Core.forEachChild(Core.withoutStanding(node),
                child -> under[0] &= WhatARunMayEndFor.endsNoneBeneath(child));
        return under[0];
    }

    /**
     * Whether {@code node} is a place of the input read as it is: a name or a field of one, with
     * no call or operation between it and the place. A row is built with the number at such a
     * place, so the representation it has is the one the row is built with.
     */
    private static boolean isAPlainRead(Core node) {
        Core at = Core.withoutStanding(node);
        while (true) {
            switch (at) {
                case Core.Read _ -> {
                    return true;
                }
                case Core.FieldAccess access -> at = Core.withoutStanding(access.target());
                case Core.FieldProjection projection -> at = Core.withoutStanding(projection.base());
                default -> {
                    return false;
                }
            }
        }
    }

    /** What a reading of a comparison was told as it went: the operations of whole numbers, and
     *  whether nothing it read could stop a run without telling. */
    private static final class WhatWasTold {

        private final List<UndividedByARelation.IntOperation> operations = new ArrayList<>();
        /** The node each of {@link #operations} was told at, by where it is among them. */
        private final List<Core> at = new ArrayList<>();
        /** The operations of decimals, in the order they were told. */
        private final List<DecimalOperation> decimals = new ArrayList<>();
        /** Where in {@link #decimals} the operation a form is the result of is, by the form. */
        private final Map<LinearForm<NumericTerm>, Integer> resultOf = new IdentityHashMap<>();
        /** The forms that are a place of the input read as it is, a number a row is built with. */
        private final Set<LinearForm<NumericTerm>> inputReads =
                Collections.newSetFromMap(new IdentityHashMap<>());
        /** The forms of the operations over a stopped value that are told of nowhere, to be asked
         *  of the form of the comparison. */
        private final List<LinearForm<NumericTerm>> sumsOverTheStop = new ArrayList<>();
        private boolean exact = true;

        void add(Core node, UndividedByARelation.IntOperation operation) {
            at.add(Core.withoutStanding(node));
            operations.add(operation);
        }

        /**
         * The operations already told that {@code node} is worked out of: those told at one of
         * its operands, and theirs. The walk tells of an operand before what it is an operand of,
         * so the last told at the operand is one this run works out before {@code node}. A node
         * read twice — a definition, or a name bound once and read on both sides — is told twice,
         * and the copy told first is missed. That leaves out only what comes after, never puts in
         * what does not: a run is then taken to stop at either copy first, and the two are past
         * their types at the same rows, which are said of neither. An operand worked out by a call
         * is told at no node of its own and is missed the same way.
         */
        List<Integer> workedOutOf(Core node) {
            return workedOutOf(switch (Core.withoutStanding(node)) {
                case Core.Neg neg -> List.of(neg.operand());
                case Core.Binary binary -> List.of(binary.left(), binary.right());
                default -> List.<Core>of();
            });
        }

        /** The same, of a node worked out of {@code operands}. */
        List<Integer> workedOutOf(List<Core> operands) {
            List<Integer> out = new ArrayList<>();
            for (Core operand : operands) {
                Core bare = Core.withoutStanding(operand);
                for (int i = at.size() - 1; i >= 0; i--) {
                    if (at.get(i) == bare) {
                        out.add(i);
                        out.addAll(operations.get(i).after());
                        break;
                    }
                }
            }
            return out;
        }

        /**
         * Tells {@code operation}, a sum, a difference or a product of decimals, as an operation a
         * row is asked by working it out, over the numbers of {@code operands}; false where it is
         * none of those, and nothing is told.
         *
         * <p>An operand is told only where the scale it is worked out at is known, since the scale
         * is what a decimal operation has room for: a decimal as the program wrote it; the result
         * of an operation told before, at the scale that operation left; or a number the row
         * itself holds, which the row is built with at the fewest places. An operand that is
         * anything else — a negated value, a constant the program folded, a call's answer — has a
         * scale nothing here knows, and the operation is then not told: no row is shown to get
         * past it.
         *
         * <p>An operand is known by the form it was composed as, which a name carries to where it
         * is read: {@code let x = h.value} reads {@code x} as the form of {@code h.value}.
         */
        boolean addsDecimal(Core operation, LinearForm<NumericTerm> result,
                            List<LinearForm<NumericTerm>> operands) {
            if (!(Core.withoutStanding(operation) instanceof Core.Binary binary)
                    || binary.type() != Type.DECIMAL
                    || (binary.op() != BinOp.ADD && binary.op() != BinOp.SUB
                    && binary.op() != BinOp.MUL)
                    || operands.size() != 2) {
                return false;
            }
            List<DecimalOperation.Operand> over = new ArrayList<>();
            List<Integer> after = new ArrayList<>();
            List<Core> written = List.of(binary.left(), binary.right());
            for (int i = 0; i < 2; i++) {
                DecimalOperation.Operand operand = operandOf(written.get(i), operands.get(i));
                if (operand == null) {
                    return false;
                }
                over.add(operand);
                if (operand instanceof DecimalOperation.Worked worked) {
                    after.add(worked.operation());
                    after.addAll(decimals.get(worked.operation()).after());
                }
            }
            DecimalOperation told = new DecimalOperation(binary.op(), over, after);
            int at = decimals.indexOf(told);
            if (at < 0) {
                at = decimals.size();
                decimals.add(told);
            }
            resultOf.put(result, at);
            return true;
        }

        /** What {@code node}, composed as {@code form}, is worked out of by an operation of
         *  decimals, or null where the scale it has is not known. */
        private DecimalOperation.Operand operandOf(Core node, LinearForm<NumericTerm> form) {
            Core bare = Core.withoutStanding(node);
            if (bare instanceof Core.Decimal literal) {
                return new DecimalOperation.Written(literal.value());
            }
            if (bare instanceof Core.Neg negated
                    && Core.withoutStanding(negated.operand()) instanceof Core.Decimal literal) {
                return new DecimalOperation.Written(literal.value().negate());
            }
            Integer worked = resultOf.get(form);
            if (worked != null) {
                return new DecimalOperation.Worked(worked);
            }
            if (inputReads.contains(form)) {
                return new DecimalOperation.Formed(
                        new LinkedHashMap<Object, ExactRatio>(form.coefs()), form.constant());
            }
            return null;
        }

        /** That {@code form} is the number a row holds at a place of the input, read as it is. */
        void readsTheInput(LinearForm<NumericTerm> form) {
            inputReads.add(form);
        }

        UndividedByARelation.Working working() {
            return new UndividedByARelation.Working(operations, exact
                    ? WhatARelationLeavesUndivided.Told.EVERY
                    : WhatARelationLeavesUndivided.Told.SOME,
                    true, decimals);
        }
    }

    /**
     * What a run works out to decide which arm of {@code choice} it takes, which every run of an
     * arm has worked out first: what evaluating the choice reaches before any arm. A comparison
     * among it is read as any is, its two sides worked out whichever way it comes out; anything
     * else that can stop a run tells nothing.
     */
    static UndividedByARelation.Working workingOfWhatDecides(Core choice, InputReads at,
                                                             InputReading ofTheInput) {
        UndividedByARelation.Working together = new UndividedByARelation.Working(List.of(),
                WhatARelationLeavesUndivided.Told.EVERY);
        for (Evaluated.Step step : Evaluated.inOrder(choice)) {
            UndividedByARelation.Working here = switch (step) {
                case Evaluated.Step.Always always ->
                        workingOfEvaluating(always.expression(), at, ofTheInput);
                case Evaluated.Step.OnlyWhere only ->
                        WhatARunMayEndFor.endsNoneBeneath(only.expression())
                                ? new UndividedByARelation.Working(List.of(),
                                        WhatARelationLeavesUndivided.Told.EVERY)
                                : UndividedByARelation.Working.UNREAD;
            };
            together = here.after(together);
        }
        return together;
    }

    private static UndividedByARelation.Working workingOfEvaluating(Core expression, InputReads at,
                                                                    InputReading ofTheInput) {
        if (WhatARunMayEndFor.endsNoneBeneath(expression)) {
            return new UndividedByARelation.Working(List.of(),
                    WhatARelationLeavesUndivided.Told.EVERY);
        }
        if (!(Core.withoutStanding(expression) instanceof Core.Binary comparison)
                || !comparison.op().compares()) {
            return UndividedByARelation.Working.UNREAD;
        }
        WhatWasTold told = new WhatWasTold();
        AffineForms.Reading<NumericTerm, InputReads> reading = reading(ofTheInput,
                new LinkedHashSet<>(), new ElementsMet(), told);
        for (Core side : List.of(comparison.left(), comparison.right())) {
            if (AffineForms.outcome(side, at, reading)
                    instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads>) {
                told.exact = false;
            }
        }
        return told.working();
    }

    /** What {@code side} comes to once the bindings written around it are taken off. */
    static Core withoutBindings(Core side) {
        Core value = Core.withoutStanding(side);
        while (value instanceof Core.LetIn binding) {
            value = Core.withoutStanding(binding.body());
        }
        return value;
    }

    /**
     * The expressions nothing reads, held aside while the rest of a comparison is read: the one
     * the reading stopped at, and any other. Each stands for an atom of its own, no position of
     * the input, so that what is proved of one — the numbers it comes to, that its owner answers
     * for it — is proved of that one and of no other that was held aside as well.
     *
     * <p>The stopped expression is read as a quotient by a value on the rows whose divisor is not
     * nought where {@code quotientAwayFromNought} says so, and then the dividend and the divisor
     * are worked out on them and told.
     */
    private static final class StoppedValues {

        private final Core stop;
        private final boolean quotientAwayFromNought;
        private final InputReading read;
        private final Predicate<Core> answersFor;
        private final Map<Core, Held> byExpression = new IdentityHashMap<>();
        private final Map<NumericTerm, Held> byAtom = new LinkedHashMap<>();
        private Held theStop;

        StoppedValues(Core stop, boolean quotientAwayFromNought, InputReading read,
                      Predicate<Core> answersFor) {
            this.stop = Objects.requireNonNull(stop);
            this.quotientAwayFromNought = quotientAwayFromNought;
            this.read = Objects.requireNonNull(read);
            this.answersFor = Objects.requireNonNull(answersFor);
        }

        /** One expression held aside, and what is known of the numbers it comes to. */
        private static final class Held {

            private final NumericTerm atom;
            private final boolean aChoice;
            private final boolean theStop;
            private boolean met;
            private FormRange range;

            Held(NumericTerm atom, Core expression, boolean theStop) {
                this.atom = atom;
                this.aChoice = Choice.of(Core.withoutStanding(expression)) != null;
                this.theStop = theStop;
            }

            /** Whether this is the first time the expression was met, so that it is answered for
             *  once however often the walk reads it. */
            boolean firstMeeting() {
                boolean first = !met;
                met = true;
                return first;
            }

            void rangeIs(FormRange range) {
                this.range = range;
            }
        }

        /** The atom {@code expression} stands for, the same one wherever the same expression is
         *  read, and the stopped expression's wherever that is. */
        Held holdAside(Core expression) {
            Core bare = Core.withoutStanding(expression);
            Held held = byExpression.get(bare);
            if (held == null) {
                if (stop.equals(expression)) {
                    if (theStop == null) {
                        theStop = newHeld(expression, true);
                    }
                    held = theStop;
                } else {
                    held = newHeld(expression, false);
                }
                byExpression.put(bare, held);
            }
            return held;
        }

        private Held newHeld(Core expression, boolean isTheStop) {
            NumericTerm atom = new NumericTerm.ValueOf(
                    TermPath.of("the expression held aside #" + byAtom.size()));
            Held held = new Held(atom, expression, isTheStop);
            byAtom.put(atom, held);
            return held;
        }

        /** What {@code form} holds aside. */
        List<Held> heldIn(LinearForm<NumericTerm> form) {
            List<Held> out = new ArrayList<>();
            for (NumericTerm atom : form.coefs().keySet()) {
                Held held = byAtom.get(atom);
                if (held != null) {
                    out.add(held);
                }
            }
            return out;
        }

        /** The numbers each expression held aside comes to, null where that is not known. */
        Map<NumericTerm, FormRange> ranges() {
            Map<NumericTerm, FormRange> out = new HashMap<>();
            byAtom.forEach((atom, held) -> out.put(atom, held.range));
            return out;
        }

        /** Whether the analysis that drew the lines answers for {@code other}, an expression
         *  beside the stopped one, as it does for that one. */
        boolean answersFor(Core other) {
            return answersFor.test(other);
        }

        /** Whether {@code held} is the stopped expression, and neither a choice nor a quotient by
         *  a value. */
        boolean isAPlainStop(Held held) {
            return held.theStop && !held.aChoice && !quotientAwayFromNought;
        }

        boolean quotientAwayFromNought() {
            return quotientAwayFromNought;
        }

        InputReading read() {
            return read;
        }
    }

    /**
     * What a comparison works out beside the expression its reading stopped at, read once and
     * only when a line drawn from the stopped reading asks.
     */
    static final class WhatLiesBesideTheStop {

        private final StatedComparison comparison;
        private final InputReads reads;
        private final InputReading ofTheInput;
        private final Core node;

        WhatLiesBesideTheStop(StatedComparison comparison, InputReads reads,
                              InputReading ofTheInput, Core node) {
            this.comparison = Objects.requireNonNull(comparison);
            this.reads = Objects.requireNonNull(reads);
            this.ofTheInput = Objects.requireNonNull(ofTheInput);
            this.node = Objects.requireNonNull(node);
        }

        /**
         * What is worked out beside the stop, where nothing of the stopped value is told: the
         * operations beside it are every one that is told, and the sizes of the form answer for a
         * row where there are none.
         */
        UndividedByARelation.Working apart(Predicate<Core> answersFor) {
            UndividedByARelation.Working beside =
                    beside(new StoppedValues(node, false, ofTheInput, answersFor));
            return beside.operations().isEmpty() && beside.exact()
                    ? UndividedByARelation.Working.NOTHING : beside;
        }

        /** The same for the quotient {@code division}, which the analysis answers for with
         *  everything written under it and under the expression the reading stopped at, which it
         *  reads the quotient out of. */
        UndividedByARelation.Working ofTheQuotientAwayFromNought(Core division) {
            Set<Core> under = Collections.newSetFromMap(new IdentityHashMap<>());
            collectUnder(division, under);
            collectUnder(node, under);
            return beside(new StoppedValues(division, true, ofTheInput,
                    node -> under.contains(Core.withoutStanding(node))));
        }

        private static void collectUnder(Core around, Set<Core> into) {
            Core here = Core.withoutStanding(around);
            into.add(here);
            Core.forEachChild(here, child -> collectUnder(child, into));
        }

        private UndividedByARelation.Working beside(StoppedValues stoppedAt) {
            WhatWasTold told = new WhatWasTold();
            AffineForms.Reading<NumericTerm, InputReads> reading = reading(ofTheInput,
                    new LinkedHashSet<>(), new ElementsMet(), told, stoppedAt);
            List<LinearForm<NumericTerm>> sides = new ArrayList<>();
            for (Core side : List.of(comparison.left(), comparison.right())) {
                // A second stop is one more expression nothing is told of.
                if (AffineForms.outcome(side, reads, reading)
                        instanceof AffineForms.Outcome.Composed<NumericTerm, InputReads> read) {
                    sides.add(read.form());
                } else {
                    told.exact = false;
                }
            }
            LinearForm<NumericTerm> whole = sides.size() == 2 ? sides.get(0).minus(sides.get(1))
                    .orNull() : null;
            for (LinearForm<NumericTerm> sum : told.sumsOverTheStop) {
                if (!areAddendsOf(sum, whole)) {
                    told.exact = false;
                }
            }
            // The stopped expression is worked out too, and a run may stop in it before any
            // operation told.
            return told.working().notOnEveryRun();
        }

        /**
         * Whether {@code sum} adds up addends of {@code whole}, the form the comparison is a
         * cut of, each as large as it weighs there. That is all the program is taken to work
         * out where the sizes of the addends answer for a row: a size has no sign, and which side
         * of the comparison an addend was written on only turns it round. A sum with a constant,
         * or weighing an addend differently, is an operation of its own.
         */
        private static boolean areAddendsOf(LinearForm<NumericTerm> sum,
                                            LinearForm<NumericTerm> whole) {
            return whole != null && sum.constant().signum() == 0
                    && sum.coefs().entrySet().stream().allMatch(each -> {
                        ExactRatio weighs = whole.coefs().get(each.getKey());
                        return weighs != null && each.getValue().abs().equals(weighs.abs());
                    });
        }
    }

    /** The one position this cuts where it cuts one with a coefficient of one, or null. A form
     *  written {@code -x} has already been turned round by the reading that made it
     *  ({@link #read}), so this asks about the coefficient as the canonical form has it. */
    NumericTerm oneCoordinate() {
        if (form.coefs().size() != 1) {
            return null;
        }
        Map.Entry<NumericTerm, ExactRatio> only = form.coefs().entrySet().iterator().next();
        return only.getValue().equals(ExactRatio.ONE) ? only.getKey() : null;
    }

    /**
     * The two positions this holds apart, as {@code on} and {@code against}, or null where it holds
     * no two apart.
     *
     * <p>Coefficients of one and minus one, which is what makes the quantity a distance: {@code 2a -
     * b} is not how far two positions stand apart, it is an arithmetic form over both of them.
     */
    NumericTerm[] twoCoordinates() {
        return twoCoordinates(form);
    }

    /**
     * The same of any form of the input's numbers, for every reader that asks which two positions
     * a form holds apart: the line a comparison draws and the quantity a row is read at are one
     * question about the form.
     */
    static NumericTerm[] twoCoordinates(LinearForm<NumericTerm> form) {
        if (form.coefs().size() != 2) {
            return null;
        }
        NumericTerm on = null;
        NumericTerm against = null;
        for (Map.Entry<NumericTerm, ExactRatio> each : form.coefs().entrySet()) {
            if (each.getValue().equals(ExactRatio.ONE)) {
                on = each.getKey();
            } else if (each.getValue().equals(ExactRatio.ONE.negated())) {
                against = each.getKey();
            }
        }
        return on == null || against == null ? null : new NumericTerm[] {on, against};
    }

    /**
     * The same statement with the quantity negated and the threshold and operator turned round.
     *
     * <p>{@code -x <= -5} states what {@code x >= 5} states. Which of the two a reading meets is
     * whichever way the author wrote the subtraction, and it is not a difference between two rules.
     */
    private AffineReading mirrored() {
        return new AffineReading(form.negate(), cut.negated(), claim.turned());
    }

    /**
     * Whether this is the same statement written the other way round.
     *
     * <p>Which way a statement faces is the sign of one coefficient, and which coefficient is the
     * question. Where the comparison's left side names a position, that one: {@code charge > ceiling}
     * and {@code 3a - 6b <= 48} are lines about what the author put on the left, and deriving the
     * subject where the source states it would rename half the borders in a report. Where it names
     * none — {@code 48 >= 3a - 6b} — nothing is being kept, and the form's own order settles it.
     *
     * <p>Total either way, which is what makes it canonical. Settled by every coefficient being
     * negative, {@code 48 >= 3a - 6b} faced neither way and kept the quantity {@code -3a + 6b} —
     * the same line as {@code 3a - 6b <= 48} under a name no author wrote.
     */
    private boolean facesTheOtherWay(NumericTerm subject) {
        ExactRatio first = subject == null ? null : form.coefs().get(subject);
        return (first != null ? first : ordered(form).getFirst().getValue()).signum() < 0;
    }

    /** The position the comparison's left side names first among the terms of {@code left}, or null
     *  where it names none of them. Handed what was read rather than walking it again: one
     *  comparison is read once. */
    private static NumericTerm subjectOf(Core leftSide, LinearForm<NumericTerm> left,
                                         InputReads reads, RuleReadingSource ruleSource) {
        if (left == null || left.coefs().isEmpty()) {
            return null;
        }
        for (souther.compiler.inputs.TermPath named
                : GuardThresholds.mentionedIn(leftSide, reads, ruleSource.symbols(),
                        ruleSource.newtypes(),
                        // A side of a comparison and not a clause: what this is handed is the side
                        // alone, and rooting a reading of arrivals at it would read it as a tree of
                        // its own and lose whatever bound a name above it.
                        souther.compiler.coverage.Arrivals.everyArmIsTakenForAValue())) {
            for (NumericTerm atom : NumericTerms.inOrder(left.coefs().keySet())) {
                if (atom.subjectPath().equals(named)) {
                    return atom;
                }
            }
        }
        return null;
    }

    /**
     * The order each of this form's positions is read and written back on, or null where some
     * position has no order with counts under it.
     *
     * <p>Asked of each position and not of the operand it was written beside. Read off one
     * operand's type, every position of the form answered with that one's order and the check could
     * not fire at all: positions were then read off rows, and written back, on an order that is not
     * theirs.
     *
     * <p>An order apiece rather than one for all of them, and no question here about whether the
     * form adds up to anything. Which positions may be added, and with which weights, is settled
     * before this: an arithmetic a model wrote type-checked, and one this compiler composed stands
     * on what the operation states about its result. A rule refusing forms here by comparing what
     * the orders count would be a reader deciding that again, and deciding it worse — it cannot see
     * the coefficients. {@code b + a} over two dates leaves an origin in and {@code b - a - n} does
     * not, and those two are the same orders in the same numbers.
     *
     * <p>What is asked is only that each position has an order, and that the order has counts under
     * it: a position with no number is one a sum has nothing to add.
     */
    java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> carriers(
            souther.compiler.inputs.Quantities quantities) {
        java.util.Map<NumericTerm, souther.compiler.inputs.TermOrders> on =
                new java.util.LinkedHashMap<>();
        for (NumericTerm term : NumericTerms.inOrder(form.coefs().keySet())) {
            // Both ends of the term, because a reader of a row wants the one it is decoded on and a
            // reader of a line wants the one the answer is measured on. Carried together so neither
            // stands in for the other (#1027).
            souther.compiler.inputs.TermOrders here = quantities.ordersOf(term);
            if (here.answered() == null || !here.answered().counts()) {
                return null;
            }
            on.put(term, here);
        }
        return on.isEmpty() ? null : on;
    }

    /** Whether the operator orders the values around the threshold rather than singling one out. */
    boolean orders() {
        return claim instanceof ComparisonClaim.Cut;
    }

}
