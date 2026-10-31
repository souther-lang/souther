package souther.compiler.partition;

import souther.compiler.abort.GetsPast;
import souther.compiler.check.AffineForms;
import souther.compiler.check.Choice;
import souther.compiler.check.ClausesInOrder;
import souther.compiler.check.CallArguments;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.TypeView;
import souther.compiler.check.ValueStanding;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.Location;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.RoundedToAWholeNumber;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.WalkElements;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.core.Kernel;
import souther.compiler.inputs.DecimalOperation;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ElementValue;
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
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TotalsOfOneRun;
import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.TakenAs;
import souther.compiler.semantics.WhereAnOperatorAnswers;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Stream;
import java.util.function.Predicate;
import java.util.stream.IntStream;

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

    /** The library's widening of a whole number to a decimal: exact, and no place past the
     *  point. */
    private static final ValueName.Stdlib.Operation WIDENS_A_WHOLE_NUMBER =
            ValueName.Stdlib.operation("Decimal", "fromInt");

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
         * comparison is read again with the stopped value held aside ({@link Stopped#apart}).
         * Where neither working that value out nor anything beside it can stop a row the lines
         * are answered for their rows by the form's sizes
         * ({@link UndividedByARelation.Working#NOTHING}); where something can, the operations
         * told are kept and the rest is not told. That analysis reads the number the value comes
         * to, which says nothing of whether working it out gets there.
         */
        static UndividedByARelation.Working workingOf(OfAComparison read) {
            return worksOut(read).toGetPast();
        }

        /** The same, with what a run getting to the comparison works out, off the one reading. */
        static WorkedOut worksOut(OfAComparison read) {
            return switch (read) {
                case Cuts cuts -> WorkedOut.ofWhatIsToldOf(cuts.working());
                case Stopped stopped -> stopped.worksOut(WhatTheAnalysisAnswersFor.NOTHING);
                case CutsNothing _, NotHeld _ ->
                        WorkedOut.ofWhatIsToldOf(UndividedByARelation.Working.UNREAD);
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
             * What the program works out with the expression the reading stopped at held aside,
             * for a relation drawn on what that expression answers: none of the stopped value's
             * own operations are told, and a row is not shown computed for an operation beside it
             * that is not. {@code answersFor} says what of the expressions held aside, the stopped
             * one among them, the analysis answers for; any other that may end a run where its
             * answer has a place leaves the operations told as not every one.
             */
            UndividedByARelation.Working apart(WhatTheAnalysisAnswersFor answersFor) {
                return beside.apart(answersFor);
            }

            /** The same, with what a run getting to the comparison works out, off the one reading
             *  ({@link WhatLiesBesideTheStop#worksOut}). */
            WorkedOut worksOut(WhatTheAnalysisAnswersFor answersFor) {
                return beside.worksOut(answersFor);
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
        OfAComparison with = read(comparison, reads, ofTheInput, true);
        // A product held against a written number is a line on the product, drawn through the
        // two factors, which is not a line on a number of one place: it stays a stop here, where
        // the rule for a product reads it.
        return with == null ? read(comparison, reads, ofTheInput, false) : with;
    }

    /**
     * The same, with a product of two non-constant numbers a number of its own, or a stop;
     * null where it is a number of its own and the comparison is nothing but that product held
     * against a written number.
     */
    private static OfAComparison read(StatedComparison comparison, InputReads reads,
                                      InputReading ofTheInput, boolean productsAreNumbers) {
        InputDomain inputs = ofTheInput.domain();
        RuleReadingSource ruleSource = ofTheInput.rules();
        // What this reading names as it goes, kept so that a reading which ran to the end can say
        // what it was about without anybody reading the comparison again.
        java.util.Set<NumericTerm> named = new java.util.LinkedHashSet<>();
        // One element of each container for the whole comparison, whichever side names it.
        ElementsMet met = new ElementsMet();
        // What the two sides work out, as they are written.
        WhatWasTold told = new WhatWasTold();
        told.productsStop = !productsAreNumbers;
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
                if (productsAreNumbers && whole.coefs().size() == 1
                        && whole.coefs().keySet().iterator().next()
                        instanceof NumericTerm.ProductOf) {
                    return null;
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
                .flatMap(AffineReading::thoseItIsMadeOf)
                .<souther.compiler.inputs.FilingCoordinate>map(
                        souther.compiler.inputs.FilingCoordinate::of)
                .distinct().toList();
    }

    /** The numbers {@code term} is read of: itself, and for a product of two forms the numbers of
     *  both, each of which a rule about the product is about. */
    private static Stream<NumericTerm> thoseItIsMadeOf(NumericTerm term) {
        return term instanceof NumericTerm.ProductOf product
                ? product.factors().stream().flatMap(form -> form.coefs().keySet().stream())
                        .flatMap(AffineReading::thoseItIsMadeOf)
                : Stream.of(term);
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
    private static Arithmetic reading(
            InputReading ofTheInput, Set<NumericTerm> named, ElementsMet met, WhatWasTold told) {
        return reading(ofTheInput, named, met, told, null);
    }

    /**
     * The reading of a comparison's arithmetic, with the readings of a call it unrolls, which
     * are tried by another reading of the same input and kept only where they come to a form.
     */
    private interface Arithmetic extends AffineForms.Reading<NumericTerm, InputReads> {

        /** What a walk from a seed over a list written out at the call comes to, step by step. */
        Attempt walkOfWhatIsWrittenOut(Core node, InputReads at);

        /** What a total over what an operation makes of a list written out at it comes to,
         *  application by application. */
        Attempt totalOfWhatIsMadeOfAListWrittenOut(Core node, InputReads at);

        /** What a product of two forms of numbers comes to as a number of its own. */
        Attempt productOfTwoForms(Core node, InputReads at);
    }

    /**
     * What reading a call by one of the rules that unroll it came to.
     *
     * <p>The rules differ in whether they were about the call at all. One that was not says so and
     * the call is read some other way; one that was, and could not be carried through, says what
     * kept it, so the call is reported for that when no other rule reads it.
     */
    private sealed interface Attempt {

        /** The call is this form. */
        record Form(LinearForm<NumericTerm> form) implements Attempt {

            public Form {
                Objects.requireNonNull(form, "an attempt that came to a form has one");
            }
        }

        /** The rule is not about the call, or a part of it composes no form that says why. */
        record NotApplicable() implements Attempt {}

        /** The rule is about the call and this reading declined its work at a figure. */
        record Declined(WhyUnread why) implements Attempt {

            public Declined {
                Objects.requireNonNull(why, "an attempt declined declined for a reason");
            }
        }

        /** The rule is about the call and a part of what it reads stopped. */
        record PartStopped(AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> inside)
                implements Attempt {

            public PartStopped {
                Objects.requireNonNull(inside, "an attempt whose part stopped stopped somewhere");
            }
        }

        /** What {@code outcome}, the reading of a part, came to as the attempt it is part of. */
        static Attempt ofAPart(AffineForms.Outcome<NumericTerm, InputReads> outcome) {
            return switch (outcome) {
                case AffineForms.Outcome.Composed<NumericTerm, InputReads>(var form) ->
                        new Form(form);
                case AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> stopped ->
                        new PartStopped(stopped);
            };
        }
    }

    /**
     * The same, holding aside the value of {@code stoppedAt} where it is not null: the expression a
     * reading stopped at stands for an atom no operation is told over, so that the rest of the
     * comparison is read for what it works out.
     */
    private static Arithmetic reading(
            InputReading ofTheInput, Set<NumericTerm> named, ElementsMet met, WhatWasTold told,
            StoppedValues stoppedAt) {
        InputDomain inputs = ofTheInput.domain();
        RuleReadingSource ruleSource = ofTheInput.rules();
        ReadMeaning.WhereKept kept = KeptTruths.readIn(ofTheInput);
        return new Arithmetic() {

            /** What the walk being unrolled has carried so far, by its accumulator, while its
             *  step is read ({@link #walkOfWhatIsWrittenOut}). */
            private final Map<BindingId, LinearForm<NumericTerm>> carried = new HashMap<>();

            /** What a run works out to reach a value, asked once for each value this reading
             *  asks it of. */
            private final WorkedOutToReachIt reached = WorkedOutToReachIt.of(ofTheInput);

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
                tell(operation, form, operands, AffineForms.whereItAnswers(operation));
            }

            /**
             * A newtype's construction, told as the operation it is where the clauses of the type
             * leave a run of numbers and every number of the run: a run stops there where the
             * number it wraps is outside it, as it stops at a sum outside the ends of an
             * {@code Int}. Where they leave anything else, or the wrapped number is not an
             * {@code Int}, what stops the run is not told.
             */
            @Override
            public void constructed(Core.Construct construct, TypeView type,
                                    LinearForm<NumericTerm> value) {
                if (makingEndsNoRun(construct)) {
                    return;
                }
                WhereAnOperatorAnswers.WhereItsExactValueIsHeld where =
                        DeclaredBounds.whereMakingSucceeds(construct, type,
                                ofTheInput.ruleReading());
                if (where == null) {
                    told.exact = false;
                    return;
                }
                tell(construct, value, List.of(value), where);
            }

            /**
             * {@code operation}, worked out as {@code form} over {@code operands} where a run
             * stops at it as {@code where} says, told as the operations of this comparison.
             */
            private void tell(Core operation, LinearForm<NumericTerm> form,
                              List<LinearForm<NumericTerm>> operands,
                              WhereAnOperatorAnswers where) {
                if (heldAside(operation, where, form, told.workedOutOf(operation))) {
                    return;
                }
                if (where instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held) {
                    tellHeld(operation, held, form, told.workedOutOf(operation));
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

            /** A number read as what it folds to, which says nothing of what working it out runs on
             *  the way: where that may end a run, not every operation is told. */
            @Override
            public void folded(Core e, InputReads at) {
                if (!reached.endsNoRun(new Denotation(e, at))) {
                    told.exact = false;
                }
            }

            /** A call of the library read as arithmetic over its arguments, told as the operation
             *  it is where a run stops at it: past the ends of the type it answers, as a sum is. */
            @Override
            public void answeredByTheLibrary(Core call, LinearForm<NumericTerm> form,
                                             WhereAnOperatorAnswers where) {
                if (aDecimalMadeOfWholeNumbers(call)) {
                    told.readsTheInput(form);
                }
                tell(call, form, List.of(form), where);
            }

            /** Whether {@code call} is the library's widening of a whole number to a decimal, which
             *  holds no places beyond the point: {@code Decimal.fromInt(n)} is the number
             *  {@code n} is. Only that operation, and not any that answers a decimal from whole
             *  numbers: a division of two of them has as many places as it is asked for. */
            private boolean aDecimalMadeOfWholeNumbers(Core call) {
                return Core.withoutStanding(call) instanceof Core.PreservedCall kept
                        && kept.operation() instanceof ValueName.Stdlib.Operation operation
                        && WIDENS_A_WHOLE_NUMBER.equals(operation);
            }

            /**
             * A value bound before a body the walk read without reading the name, read as any
             * part of the comparison is, so what working it out may stop a run at is told: it is
             * worked out once before the body on every run, whichever arm the body then takes.
             *
             * <p>Not one the walk read the name of through a node it read as numbers of the input:
             * what the name was given was asked there with the node. One that composes no form is
             * told by no operation here, and gets through only where working it out ends no run
             * ({@link WorkedOutToReachIt#endsNoRun}); any other is a node read without telling of
             * every operation. That what reads the name answers on the rows of a line is no
             * evidence for the value: its answer having a place does not give this one one. Nor
             * is it that the body reads the name on another way than the walk took, since a run
             * that takes this way works the value out all the same.
             */
            @Override
            public void bound(Core.LetIn binding, InputReads at) {
                BindingId name = binding.binder() == null ? null : binding.binder().binding();
                if (name != null && told.readByATerm(name)) {
                    return;
                }
                if (tried(apart -> Attempt.ofAPart(AffineForms.outcome(binding.value(), at, apart)))
                        instanceof Attempt.Form) {
                    return;
                }
                if (reached.endsNoRun(new Denotation(binding.value(), at))) {
                    return;
                }
                if (tellsTheClosuresMakingAnOption(binding.value(), at)
                        || isARemainderOfAReadForm(binding.value(), at, this, ruleSource,
                                reached)) {
                    return;
                }
                told.exact = false;
            }

            /**
             * Whether {@code value} is an option made by closures applied to what another holds,
             * and so worked out as they are: each closure's body, read where its parameter stands
             * for what it was handed, tells its operations. A closure is applied only where the
             * option holds a value, which a row of the entry it holds is at. What else
             * {@code value} works out must end no run.
             */
            private boolean tellsTheClosuresMakingAnOption(Core value, InputReads at) {
                List<Denotation> closures = at.closuresMakingWhatItHolds(value,
                        ruleSource.symbols(), ruleSource.newtypes());
                if (closures.isEmpty()) {
                    return false;
                }
                for (Denotation closure : closures) {
                    if (AffineForms.outcome(closure.value(), closure.at(), this)
                            instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads>
                            && !reached.endsNoRun(closure)) {
                        told.exact = false;
                    }
                }
                if (!restEndsNoRun(value, at, reached, closures)) {
                    told.exact = false;
                }
                return true;
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
                tellAnIntTotal(call, total, told.workedOutOf(elements));
            }

            /**
             * The length of a list written out, whose elements are worked out as the list is
             * built. Past the figure a list is read element by element up to, they are not told.
             */
            @Override
            public void counted(Core call, List<Core> elements, InputReads at) {
                if (told.declinedAtCounting(elements.size()).isEmpty()) {
                    builtFrom(elements, at);
                } else {
                    told.exact = false;
                }
            }

            /**
             * {@code total}, which {@code node} holds to {@code Int} once it is worked out exactly,
             * told as the one operation it is, worked out after the operations {@code after}.
             */
            private void tellAnIntTotal(Core node, LinearForm<NumericTerm> total,
                                        List<Integer> after) {
                WhereAnOperatorAnswers where = WhereAnOperatorAnswers.ofATotal(Type.INT);
                if (heldAside(node, where, total, after)) {
                    return;
                }
                if (where instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held) {
                    tellHeld(node, held, total, after);
                } else {
                    told.exact = false;
                }
            }

            /**
             * Whether {@code form} is over an expression held aside, and so told of here only as
             * its owner answers for it ({@link #stopsNoRowOrIsTheOwners}); {@code node} works it
             * out after the operations {@code after}.
             */
            private boolean heldAside(Core node, WhereAnOperatorAnswers where,
                                      LinearForm<NumericTerm> form, List<Integer> after) {
                List<StoppedValues.Held> over = stoppedAt == null ? List.of()
                        : stoppedAt.heldIn(form);
                if (over.isEmpty()) {
                    return false;
                }
                if (!stopsNoRowOrIsTheOwners(node, where, form, over, after)) {
                    told.exact = false;
                }
                return true;
            }

            /**
             * {@code form}, worked out by {@code node} and held to the ends {@code held} says,
             * told unless no row of the places it is over stops at it: such a one is not an
             * operation a run can stop at, and there is nothing to tell of it.
             */
            private void tellHeld(Core node, WhereAnOperatorAnswers.WhereItsExactValueIsHeld held,
                                  LinearForm<NumericTerm> form, List<Integer> after) {
                UndividedByARelation.IntOperation operation =
                        UndividedByARelation.IntOperation.overTheInput(form, held.least(),
                                held.greatest(), after);
                if (!FormRange.liesWithin(form, ofTheInput, Map.of(), held.least(), held.greatest())
                        && !told.operations.contains(operation)) {
                    told.add(node, operation);
                }
            }

            /**
             * Whether {@code node}, an expression nothing here reads other than the stopped one,
             * ends no run, with what each name read in it was given, or is one the analysis that
             * drew the lines answers for. Any other that may end a run has no owner here.
             */
            private boolean worksOutNothingBesideTheStop(Core node, InputReads at) {
                return reached.endsNoRun(new Denotation(node, at)) || stoppedAt.answersFor(node);
            }

            /**
             * Whether what working out {@code node}, the expression the reading stopped at, may stop
             * a run at is answered for: it ends one only where its answer has no place, which a row
             * on a line drawn on that answer is not at, or the analysis that drew the lines says it
             * answers for it. A number the lines are drawn on is the value working the expression
             * out comes to, which says nothing of whether it gets there.
             */
            private boolean theStopIsAnsweredFor(Core node, InputReads at) {
                return reached.endsOnlyWhereItsAnswerHasNoPlace(new Denotation(node, at))
                        || stoppedAt.answersFor(node)
                        || addsUpTheFormItIsReadAs(node, at)
                        || countsAListThatEndsOnlyWhereItHasNoPlace(node, at);
            }

            /**
             * Whether {@code node} is the count of a list whose working out ends a run only where
             * the list it makes has no place, and so is answered for where the comparison's line
             * on the count is at a count a list holds: a row on that line has a list with a place,
             * so working the list out ends no run there. That the count has a place says nothing of
             * the list's where the line is past what a list holds. The line is the form of the
             * whole comparison, which is not known until it is read, so it is asked of it then
             * ({@link WhatLiesBesideTheStop}).
             */
            private boolean countsAListThatEndsOnlyWhereItHasNoPlace(Core node, InputReads at) {
                if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)
                        || call.args().size() != 1
                        || !(call.operation() instanceof ValueName.Stdlib.Operation operation)
                        || ruleSource.symbols().kernelOf(operation) != Kernel.LIST_LENGTH
                        || !theListEndsOnlyWhereItHasNoPlace(
                                new Denotation(call.args().get(0), at))) {
                    return false;
                }
                told.countsOverTheStop.add(stoppedAt.holdAside(node).atom);
                return true;
            }

            /** Whether {@code list}, or what a name it is was given, ends a run only where the
             *  list it makes has no place. */
            private boolean theListEndsOnlyWhereItHasNoPlace(Denotation list) {
                if (Core.withoutStanding(list.value()) instanceof Core.Read) {
                    List<Denotation> given = reached.boundTo(list);
                    return !given.isEmpty() && given.stream()
                            .allMatch(this::theListEndsOnlyWhereItHasNoPlace);
                }
                return reached.endsOnlyWhereItsAnswerHasNoPlace(list);
            }

            /**
             * Whether working {@code node} out does no more than the analysis that drew the lines
             * reads it by: the form of one operand, which it builds its rows where adding up is
             * worked out. Read apart, the operand composes and nothing is left untold; every
             * other part of {@code node} ends no run. Every operation on the way adds up addends
             * of its form, or is told as an operation of its own. The addends' sums are the
             * witness's to keep within their type, and are no operation a row of a line is asked
             * to get past; a run works them out all the same, before anything is divided, and
             * they are kept for where a run stops ({@link WhatWasTold#leftToTheWitness}).
             */
            private boolean addsUpTheFormItIsReadAs(Core node, InputReads at) {
                Core operand = stoppedAt.readByTheFormOf(node);
                if (operand == null) {
                    return false;
                }
                boolean[] rest = {true};
                Core.forEachChild(Core.withoutStanding(node), child -> rest[0] &=
                        child == operand || reached.endsNoRun(new Denotation(child, at)));
                WhatWasTold apart = new WhatWasTold();
                LinearForm<NumericTerm> form = rest[0] ? composedBy(operand, at,
                        reading(ofTheInput, new LinkedHashSet<>(), met.copied(), apart)) : null;
                if (form == null || !apart.exact || !apart.partials.isEmpty()
                        || !apart.decimals.isEmpty()) {
                    return false;
                }
                // An operation that is no addend of the form, a sum with a number it is moved
                // by, is one the analysis asks of its own rows, so it is told here.
                if (!apart.operations.stream().allMatch(each -> each.overTheInput() != null
                        && WhatLiesBesideTheStop.areAddendsOf(each.overTheInput(), form))) {
                    told.absorb(apart);
                } else {
                    told.leftToTheWitness(apart);
                }
                stoppedAt.worksOutTheFormItIsReadAs(node);
                return true;
            }

            /**
             * Whether working {@code node} out does no more than work out the dividend of the
             * remainder the analysis that drew the lines reads it as, where it does not say a row
             * is made where the dividend is worked out, every other part of it ending no run. The
             * dividend is read as it is written, a bound value in it held aside, so each operation
             * on the way is told in the order a run works it out, over that value where it is
             * over it: {@code (a + n) + 1} is past its type at {@code a + n} before the sum is,
             * and {@code x + 1} past it where {@code x} is the greatest an {@code Int} holds,
             * though a remainder of it is one of {@code x}. All of it is told for where a run
             * stops alone ({@link WhatWasTold#besideTheRows}). A dividend over two bound values,
             * or with anything else that may stop a run, is not read so.
             */
            private boolean worksOutADividendBesideTheRows(Core node, InputReads at) {
                Core dividend = stoppedAt.dividendBesideTheRows(node);
                if (dividend == null) {
                    return false;
                }
                boolean[] rest = {true};
                Core.forEachChild(Core.withoutStanding(node), child -> rest[0] &=
                        child == dividend || reached.endsNoRun(new Denotation(child, at)));
                Set<Core> bound = new LinkedHashSet<>();
                collectBoundValues(dividend, at, bound);
                if (!rest[0] || bound.size() > 1) {
                    return false;
                }
                WhatWasTold apart = told.apart();
                StoppedValues byTheValue = bound.isEmpty() ? null
                        : stoppedAt.heldAt(bound.iterator().next());
                if (composedBy(dividend, at, reading(ofTheInput, new LinkedHashSet<>(),
                        met.copied(), apart, byTheValue)) == null
                        || !apart.partials.isEmpty() || !apart.decimals.isEmpty()) {
                    return false;
                }
                for (SumOverTheStop sum : apart.sumsOverTheStop) {
                    if (!sum.toldOverItsValue(apart, ofTheInput)) {
                        return false;
                    }
                }
                if (!apart.exact) {
                    return false;
                }
                told.besideTheRows(apart);
                stoppedAt.worksOutTheFormItIsReadAs(node);
                return true;
            }

            /** The names read under {@code e} whose value is a bound value an operation of whole
             *  numbers can be over. */
            private void collectBoundValues(Core e, InputReads at, Set<Core> into) {
                Core here = Core.withoutStanding(e);
                if (stoppedAt.boundAs(here, at) != null) {
                    into.add(here);
                }
                Core.forEachChild(here, child -> collectBoundValues(child, at, into));
            }

            /** The form {@code e} composes to as {@code by} reads it, or null where it does not. */
            private static LinearForm<NumericTerm> composedBy(
                    Core e, InputReads at, AffineForms.Reading<NumericTerm, InputReads> by) {
                return AffineForms.outcome(e, at, by)
                        instanceof AffineForms.Outcome.Composed<NumericTerm, InputReads>(
                                LinearForm<NumericTerm> form) ? form : null;
            }

            /**
             * Whether {@code form}, an operation over the expressions {@code over} held aside and
             * worked out as {@code where} says, stops no row: it answers everywhere, or the
             * numbers it comes to lie where it answers, from the numbers each expression held
             * aside is known to come to (none, for one nothing is known of). Or stops one only
             * where the analysis that owns the stopped value answers for it, which is a sum of the
             * addends of the comparison over that value and no other held aside, asked once the
             * comparison has been read ({@link WhatLiesBesideTheStop#beside}), or is an operation
             * over a bound value the derivation names, told then as the one it is. {@code node}
             * works it out after the operations {@code after}. Anything else worked out over them
             * is no owner's.
             */
            private boolean stopsNoRowOrIsTheOwners(Core node, WhereAnOperatorAnswers where,
                                                    LinearForm<NumericTerm> form,
                                                    List<StoppedValues.Held> over,
                                                    List<Integer> after) {
                if (where instanceof WhereAnOperatorAnswers.Everywhere) {
                    return true;
                }
                if (!(where instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held)) {
                    return false;
                }
                if (FormRange.liesWithin(form, stoppedAt.read(), stoppedAt.ranges(), held.least(),
                        held.greatest())) {
                    return true;
                }
                // The analysis that owns the stopped value answers for where a sum of the addends
                // of the comparison passes the ends of an Int, and for no other end: a run that
                // stops where a construction's rules refuse the number is not one it answers for.
                if (held.equals(WhereAnOperatorAnswers.WHAT_AN_INT_HOLDS)
                        && over.size() == 1 && stoppedAt.isAPlainStop(over.get(0))) {
                    told.sumsOverTheStop.add(new SumOverTheStop(node, form, over.get(0),
                            held.least(), held.greatest(), after));
                    return true;
                }
                return false;
            }

            @Override
            public Optional<AffineForms.ListWrittenOut<InputReads>> listItStandsAt(
                    Core container, InputReads at) {
                return WrittenOutElements.listItStandsAt(new Denotation(container, at),
                        ruleSource.symbols(), ruleSource.newtypes());
            }

            @Override
            public boolean makingEndsNoRun(Core.Construct construct) {
                return ClausesInOrder.at(construct, ruleSource).governsNothing();
            }

            /**
             * A newtype over an {@code Int} written out is made without ending a run where the
             * number it wraps lies in the run its clauses leave: the same run a worked-out number
             * is held to when the construction is told, asked of one that is written.
             */
            @Override
            public boolean makingEndsNoRunOver(Core.Construct construct, Core wrapped) {
                if (makingEndsNoRun(construct)) {
                    return true;
                }
                if (wrapped == null
                        || !(Core.withoutStanding(wrapped) instanceof Core.Int written)) {
                    return false;
                }
                WhereAnOperatorAnswers.WhereItsExactValueIsHeld where =
                        DeclaredBounds.whereMakingSucceeds(construct,
                                TypeView.asWritten(Type.ref(construct.typeName()), symbols(),
                                        declarations().kinds(), declarations().sums()),
                                ofTheInput.ruleReading());
                BigInteger number = BigInteger.valueOf(written.value());
                return where != null && where.least().compareTo(number) <= 0
                        && number.compareTo(where.greatest()) <= 0;
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
                return leaf(node, at, null) instanceof AffineForms.Leaf.Form<NumericTerm,
                        InputReads>(var form) ? form : null;
            }

            /**
             * {@code node} as a form of the input's numbers, or the stop it came to where the
             * rules that unroll a call were about it and none carried through.
             *
             * <p>Of those rules the first that was about the call and kept the reading from it at a
             * figure of this compiler's work is the reason: a call declined at a figure, or one
             * whose part was. A part that stopped for any other reason is not reported here; the
             * call is read some other way, or stops as it does for a call with no rule.
             */
            @Override
            public AffineForms.Leaf<NumericTerm, InputReads> leaf(
                    Core node, InputReads at,
                    AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> inside) {
                if (Core.withoutStanding(node) instanceof Core.Read name
                        && carried.get(name.binding()) instanceof LinearForm<NumericTerm> so) {
                    return new AffineForms.Leaf.Form<>(so);
                }
                // What two numbers of the input come to multiplied, where the arithmetic stopped at
                // the product itself: one number, whichever factor was written first.
                if (Core.withoutStanding(node) instanceof Core.Binary
                        && tried(apart -> apart.productOfTwoForms(node, at))
                        instanceof Attempt.Form(var product)) {
                    return new AffineForms.Leaf.Form<>(product);
                }
                AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> keptAtAFigure = null;
                // Each reading below is of a call the library's operations keep, and asked of
                // nothing else, since what it puts back where it reads nothing is copied first.
                if (Core.withoutStanding(node) instanceof Core.PreservedCall) {
                    Attempt walked = tried(apart -> apart.walkOfWhatIsWrittenOut(node, at));
                    if (walked instanceof Attempt.Form(var form)) {
                        return new AffineForms.Leaf.Form<>(form);
                    }
                    LinearForm<NumericTerm> added = walkAddingOverAContainer(node, at);
                    if (added != null) {
                        return new AffineForms.Leaf.Form<>(added);
                    }
                    Attempt applied =
                            tried(apart -> apart.totalOfWhatIsMadeOfAListWrittenOut(node, at));
                    if (applied instanceof Attempt.Form(var form)) {
                        return new AffineForms.Leaf.Form<>(form);
                    }
                    keptAtAFigure = stopAtAFigure(node, at, walked);
                    if (keptAtAFigure == null) {
                        keptAtAFigure = stopAtAFigure(node, at, applied);
                    }
                }
                LinearForm<NumericTerm> numbers =
                        InputNumber.formOf(node, inputs, at, ruleSource, met);
                if (numbers != null) {
                    named.addAll(numbers.coefs().keySet());
                    // A number worked out by a run that may stop, and no operation here tells
                    // where. What may stop one is its owners' to say, and a node they do not say
                    // of is one that may. What each name it reads was given is asked with it, so
                    // a binding of one of them is answered for here.
                    if (!NumbersOnTheWayToATotal.completeWhereTheAnswerHasAPlace(node, numbers,
                            ofTheInput, at)) {
                        NumericTerm total = addedAsItIs(numbers);
                        if (total instanceof NumericTerm.TakenOver && sumsProductsOfFields(node,
                                total)) {
                            tellAnIntTotal(node, numbers, List.of());
                            told.partials.add(total);
                        } else {
                            told.exact = false;
                        }
                    }
                    told.readByATerm(node);
                    if (isAPlainRead(node) || aDecimalMadeOfWholeNumbers(node)) {
                        told.readsTheInput(numbers);
                    }
                    return new AffineForms.Leaf.Form<>(numbers);
                }
                if (stoppedAt == null) {
                    return keptAtAFigure == null ? new AffineForms.Leaf.None<>()
                            : new AffineForms.Leaf.Stopped<>(keptAtAFigure);
                }
                // Each expression nothing here reads is held aside as an atom of its own, and what
                // working it out may stop a run at is told by nothing here. Where it may stop one
                // and the analysis that drew the lines does not say it answers for that, the
                // operations are not every one.
                StoppedValues.Held aside = stoppedAt.holdAside(node);
                if (aside.firstMeeting()) {
                    aside.boundIs(stoppedAt.boundAs(node, at));
                    if (!aside.theStop) {
                        if (!worksOutNothingBesideTheStop(node, at)
                                && !roundingWorkedOut(node, at, aside)) {
                            told.exact = false;
                        }
                    } else if (stoppedAt.quotientAwayFromNought()) {
                        operandsOfTheQuotient(node, at);
                    } else if (!theStopIsAnsweredFor(node, at)
                            && !roundingWorkedOut(node, at, aside)
                            && !worksOutADividendBesideTheRows(node, at)) {
                        told.exact = false;
                    }
                    if (aside.aChoice) {
                        aside.rangeIs(rangeOfTheArms(node, at));
                    }
                }
                return new AffineForms.Leaf.Form<>(LinearForm.atom(aside.atom));
            }

            /**
             * The stop at {@code node} that {@code attempt} comes to, where it kept the reading
             * from the call at a figure of this compiler's work — the call's own, or a part's —
             * and null where it did not.
             */
            private static AffineForms.Outcome.StoppedAt<NumericTerm, InputReads> stopAtAFigure(
                    Core node, InputReads at, Attempt attempt) {
                return switch (attempt) {
                    case Attempt.Declined(var why) -> new AffineForms.Outcome.StoppedAt<>(node, at,
                            new AffineForms.Halt.DeclinedAtAFigure<>(why));
                    case Attempt.PartStopped(var inside)
                            when inside.why().declinedFigure().isPresent() ->
                            new AffineForms.Outcome.StoppedAt<>(node, at,
                                    new AffineForms.Halt.AnArgumentStopped<>(inside));
                    case Attempt.PartStopped _, Attempt.NotApplicable _, Attempt.Form _ -> null;
                };
            }

            /**
             * The product of two forms of whole numbers {@code node} is, as a number of its own, or
             * null where it is no such product: a form of the first and a form of the second, each
             * read as any is, the numbers of the two apart.
             *
             * <p>The multiplication is told as the operation it is: the product is a number of its
             * own, so a run stops at it where that number passes the ends of an {@code Int}.
             */
            @Override
            public Attempt productOfTwoForms(Core node, InputReads at) {
                LinearForm<NumericTerm> product = productFormOf(node, at);
                return product == null ? new Attempt.NotApplicable() : new Attempt.Form(product);
            }

            private LinearForm<NumericTerm> productFormOf(Core node, InputReads at) {
                if (told.productsStop || !(Core.withoutStanding(node) instanceof Core.Binary mul)
                        || mul.op() != BinOp.MUL
                        || (mul.type() != Type.INT && mul.type() != Type.DECIMAL)) {
                    return null;
                }
                LinearForm<NumericTerm> left = composedBy(mul.left(), at, this);
                LinearForm<NumericTerm> right =
                        left == null ? null : composedBy(mul.right(), at, this);
                NumericTerm.ProductOf.Signed made =
                        right == null ? null : NumericTerm.ProductOf.signed(left, right);
                if (made == null) {
                    return null;
                }
                NumericTerm.ProductOf.Signed product =
                        ProductDeclarations.admitted(made, ofTheInput);
                named.add(product.product());
                LinearForm<NumericTerm> atom = product.asAForm();
                if (mul.type() == Type.DECIMAL) {
                    // A decimal product has no region; a row is asked by working it out.
                    if (!told.addsDecimal(mul, atom, List.of(left, right))) {
                        told.exact = false;
                    }
                    return atom;
                }
                // Told whatever the type of the number says of it: the product is the number the
                // factors come to, which is not held to an Int by being typed as one, and a run
                // stops where it passes the ends.
                if (WhereAnOperatorAnswers.ofAnOperator(BinOp.MUL, Type.INT,
                        List.of(Type.INT, Type.INT))
                        instanceof WhereAnOperatorAnswers.WhereItsExactValueIsHeld held) {
                    told.add(mul, UndividedByARelation.IntOperation.overTheInput(atom,
                            held.least(), held.greatest(), told.workedOutOf(mul)));
                } else {
                    told.exact = false;
                }
                return atom;
            }

            /**
             * What {@code unrolling} comes to, read by another reading of the input that starts
             * from what this one has met and collects what it names and tells apart from it.
             * Kept only where it came to a form: then what it named, met and told is this
             * reading's, its operations after the ones told here. Where it came to none, the
             * expression is read some other way or the comparison stops at it, and nothing the
             * attempt did is left here, whatever it would have changed. What it came to instead
             * is handed back with it.
             */
            private Attempt tried(Function<Arithmetic, Attempt> unrolling) {
                Set<NumericTerm> namedApart = new LinkedHashSet<>();
                ElementsMet metApart = met.copied();
                WhatWasTold toldApart = told.apart();
                Attempt attempt = unrolling.apply(
                        reading(ofTheInput, namedApart, metApart, toldApart));
                if (attempt instanceof Attempt.Form) {
                    named.addAll(namedApart);
                    met.takes(metApart);
                    told.absorb(toldApart);
                }
                return attempt;
            }

            /**
             * Reads {@code elements}, the list a walk or a total is over, as a run builds it
             * before anything is made of it: whether or not anything reads an element, what it
             * works out is worked out.
             */
            private void builtFrom(List<Core> elements, InputReads at) {
                for (Core element : elements) {
                    if (AffineForms.outcome(element, at, this)
                            instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads>
                            && !reached.endsNoRun(new Denotation(element, at))) {
                        told.exact = false;
                    }
                }
            }

            /**
             * What a walk from a seed over a list written out at the call comes to, read the way
             * a run works it out: the list's elements, the seed, then the step once per element
             * in the list's order, with what it carried standing for the answer so far. Each
             * application's operations are told as they are met, so a row is asked to get past
             * every step and not only the total the steps come to, which is all a sum holds to
             * its type. Not applicable where it is no such walk; declined where the list is past a
             * figure of this compiler's work; and the stop of the part where one does not compose.
             *
             * <p>Only a step written at the call over a list written there: what a step reached
             * by a name works out is in no tree read here.
             */
            @Override
            public Attempt walkOfWhatIsWrittenOut(Core node, InputReads at) {
                SeededWalk walk = SeededWalk.of(node, closure ->
                        Core.withoutStanding(closure) instanceof Core.Block block ? block : null);
                if (walk == null || !walk.inTheContainersOrder()
                        || !(Core.withoutStanding(walk.container()) instanceof Core.ListLit list)) {
                    return new Attempt.NotApplicable();
                }
                Optional<WhyUnread> declined = told.declinedAtCounting(list.elements().size());
                if (declined.isPresent()) {
                    return new Attempt.Declined(declined.get());
                }
                builtFrom(list.elements(), at);
                Attempt seeded = Attempt.ofAPart(AffineForms.outcome(walk.seed(), at, this));
                if (!(seeded instanceof Attempt.Form(LinearForm<NumericTerm> seed))) {
                    return seeded;
                }
                // What the walk does itself, apart from the step it applies.
                if (!WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(node).endsNone()) {
                    told.exact = false;
                }
                BindingId accumulator = walk.accumulator().binding();
                LinearForm<NumericTerm> so = seed;
                try {
                    for (Core element : list.elements()) {
                        InputReads handing = at.handingTheElement(walk.step(), walk.container(),
                                new Denotation(element, at), ruleSource.newtypes());
                        if (handing == null) {
                            return new Attempt.NotApplicable();
                        }
                        carried.put(accumulator, so);
                        told.after(accumulator);
                        Attempt stepped = Attempt.ofAPart(
                                AffineForms.outcome(walk.step().body(), handing, this));
                        if (!(stepped instanceof Attempt.Form(LinearForm<NumericTerm> next))) {
                            return stepped;
                        }
                        so = next;
                    }
                } finally {
                    carried.remove(accumulator);
                    told.carriedAfter.remove(accumulator);
                }
                return new Attempt.Form(so);
            }

            /**
             * What a total over the list an operation makes of a list written out at it comes
             * to, read the way a run works it out: the list's elements, then the closures written
             * at the operation once per element, each application's operations told, and last
             * the total, which is all the sum holds to its type
             * ({@link GetsPast.WhereTheTotalFits}). Not applicable where it is no such total or the
             * operation does more than apply its closures; declined where the list is past a
             * figure of this compiler's work; and the stop of the element where one it makes does
             * not compose.
             *
             * <p>Only an operation that makes every element of the list it is handed, each once:
             * one that keeps some of them answers on rows the reading would have to decide.
             */
            @Override
            public Attempt totalOfWhatIsMadeOfAListWrittenOut(Core node, InputReads at) {
                if (!(Core.withoutStanding(node) instanceof Core.PreservedCall call)
                        || !(WhatARunMayEndFor.completionApartFromTheClosuresWrittenAtIt(call)
                                instanceof GetsPast.WhereTheTotalFits(int operand))
                        || operand >= call.args().size()) {
                    return new Attempt.NotApplicable();
                }
                if (!(Core.withoutStanding(call.args().get(operand))
                        instanceof Core.PreservedCall making)) {
                    return totalOfWhatIsMadeOfWhatANameStandsFor(call, call.args().get(operand),
                            at);
                }
                if (!WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(making).endsNone()) {
                    return totalOfWhatIsMadeOfTheCodePointsOfAString(call,
                            new Denotation(call.args().get(operand), at), making, at);
                }
                // The list written out, whose elements are worked out as it is built — or the
                // number of elements of one an operation makes that works nothing out to make it
                // and whose elements the walk writes out, each a number written down.
                Core.ListLit list = null;
                InputReads listAt = at;
                Integer made = null;
                for (Core argument : making.args()) {
                    if (Core.withoutStanding(argument) instanceof Core.Block) {
                        continue;
                    }
                    Optional<AffineForms.ListWrittenOut<InputReads>> written =
                            list != null || made != null ? Optional.empty()
                                    : AffineForms.listWrittenOutBy(argument, at, this);
                    if (written.isPresent()) {
                        list = written.get().list();
                        listAt = written.get().at();
                        continue;
                    }
                    made = list != null || made != null ? null : madeWorkingNothingOut(argument, at);
                    if (made == null) {
                        return totalOfWhatIsMadeOfTheCodePointsOfAString(call,
                                new Denotation(call.args().get(operand), at), making, at);
                    }
                }
                int elements = list != null ? list.elements().size() : made != null ? made : -1;
                if (elements < 0
                        || !(WrittenOutElements.of(new Denotation(making, at),
                        ruleSource.symbols(), ruleSource.newtypes())
                        instanceof WrittenOutElements.Walked.Each each)
                        || each.asWritten().size() != elements
                        || each.asWritten().stream().anyMatch(one -> !one.keptWhere().isEmpty())) {
                    return new Attempt.NotApplicable();
                }
                Optional<WhyUnread> declined = told.declinedAtCounting(elements);
                if (declined.isPresent()) {
                    return new Attempt.Declined(declined.get());
                }
                int from = told.operations.size();
                if (list != null) {
                    builtFrom(list.elements(), listAt);
                }
                return totalOfApplications(call, from, each.asWritten().stream()
                        .map(ReadMeaning.Occurrence::value).toList());
            }

            /**
             * How many elements {@code container} holds where the walk writes out every one of
             * them, each a number written down and there on every run, and making it ends a run
             * only where the list it answers has no place — a list of every whole number between
             * two written numbers; null otherwise. The walk writing them all out is a list that
             * has a place, so making it ends no run; and nothing is built from its elements, so
             * nothing of them is told.
             */
            private Integer madeWorkingNothingOut(Core container, InputReads at) {
                if (!reached.endsOnlyWhereItsAnswerHasNoPlace(new Denotation(container, at))
                        || !(WrittenOutElements.of(new Denotation(container, at),
                        ruleSource.symbols(), ruleSource.newtypes())
                        instanceof WrittenOutElements.Walked.Each each)
                        || each.asWritten().stream().anyMatch(one -> !one.keptWhere().isEmpty()
                                || !(Core.withoutStanding(one.value().value())
                                        instanceof Core.Int))) {
                    return null;
                }
                return each.asWritten().size();
            }

            /**
             * Whether working out {@code operand}, the expression a total is taken over, and what
             * each name in it was given, ends no run apart from the closures written at
             * {@code making}, whose applications are read one by one.
             *
             * <p>Which call the operand stands for and which code points its list holds are
             * questions of values: following a name or a block to its answer leaves out what it
             * works out beside it, and that is worked out all the same. So the evaluation is
             * asked of the operand as it is written, and the values only of the walk.
             */
            private boolean theOperandEndsNoRunApartFromTheApplications(
                    Denotation operand, Core.PreservedCall making) {
                List<Core> applied = making.args().stream()
                        .filter(argument -> Core.withoutStanding(argument) instanceof Core.Block)
                        .toList();
                return reached.besideWhatWasRestated(applied, null).endsNoRun(operand);
            }

            /**
             * The same, where the operand of the total is a name that stands for the call that
             * makes the list: a code point list is read as the call it stands for is. What the
             * binding works out beside that call is asked of the binding
             * ({@link #theOperandEndsNoRunApartFromTheApplications}), and the binding is then not
             * read again.
             */
            private Attempt totalOfWhatIsMadeOfWhatANameStandsFor(Core.PreservedCall call,
                                                                 Core operand, InputReads at) {
                if (!(Core.withoutStanding(operand) instanceof Core.Read)) {
                    return new Attempt.NotApplicable();
                }
                Denotation stands = at.standing(operand, ruleSource.symbols(),
                        ruleSource.newtypes());
                if (!(Core.withoutStanding(stands.value()) instanceof Core.PreservedCall making)) {
                    return new Attempt.NotApplicable();
                }
                Attempt made = totalOfWhatIsMadeOfTheCodePointsOfAString(call,
                        new Denotation(operand, at), making, stands.at());
                if (made instanceof Attempt.Form) {
                    told.readByATerm(operand);
                }
                return made;
            }

            /**
             * What a total over what an operation makes of the code points of a string of the
             * input comes to, read application by application as a list written out is: the
             * closure's body once per code point, the position it is handed bound to the place
             * the code point stands at in the list and the code point to the one the list
             * holds there ({@link InputNumber#codePointsWalked}), then the total.
             *
             * <p>Not applicable where the operation makes something but one piece of each
             * element, or where the list is no code points of a string this follows, or the
             * string holds no number of them its rules settle; declined past a figure of this
             * compiler's work.
             */
            private Attempt totalOfWhatIsMadeOfTheCodePointsOfAString(
                    Core.PreservedCall call, Denotation operand, Core.PreservedCall making,
                    InputReads at) {
                BindingId element = WalkElements.elementBindingOf(making, at, ruleSource.symbols(),
                        ruleSource.newtypes());
                Core listed = element == null ? null : at.containerOfTheElementHandedTo(element);
                ElementAnswer closure = listed == null ? null : at.answerAt(element);
                if (closure == null || !(WhatARunMayEndFor
                        .completionApartFromTheClosuresWrittenAtIt(making)
                        instanceof GetsPast.Always)) {
                    return new Attempt.NotApplicable();
                }
                InputNumber.CodePointsWalked walked = InputNumber.codePointsWalked(listed, inputs,
                        at, ruleSource);
                if (walked == null) {
                    return new Attempt.NotApplicable();
                }
                if (!theOperandEndsNoRunApartFromTheApplications(operand, making)) {
                    told.exact = false;
                }
                Optional<WhyUnread> declined = told.declinedAtCounting(walked.indices().size());
                if (declined.isPresent()) {
                    return new Attempt.Declined(declined.get());
                }
                Denotation list = new Denotation(listed, at);
                List<Denotation> made = new ArrayList<>();
                for (int k = 0; k < walked.indices().size(); k++) {
                    InputReads handing = at.handingTheCodePointAt(element, list, k);
                    if (closure.position() != null) {
                        handing = handing.handing(closure.position(), new Denotation(
                                new Core.Int(k, Type.INT, making.pos()), at),
                                ruleSource.newtypes());
                    }
                    made.add(new Denotation(closure.body(), handing));
                }
                return totalOfApplications(call, told.operations.size(), made);
            }

            /**
             * What the total {@code call} takes of the answers of {@code made}, one application of
             * a closure each, comes to: each answer read in turn, its operations told as they are
             * met, and last the total, which is all the sum holds to its type
             * ({@link GetsPast.WhereTheTotalFits}). {@code from} is how many operations were told
             * before the first application.
             */
            private Attempt totalOfApplications(Core.PreservedCall call, int from,
                                                List<Denotation> made) {
                LinearForm<NumericTerm> total = LinearForm.constant(ExactRatio.ZERO);
                for (Denotation application : made) {
                    Attempt answered = Attempt.ofAPart(AffineForms.outcome(application.value(),
                            application.at(), this));
                    if (!(answered instanceof Attempt.Form(LinearForm<NumericTerm> one))) {
                        return answered;
                    }
                    if (!(total.plus(one) instanceof ExactAnswer.Held<LinearForm<NumericTerm>>(
                            LinearForm<NumericTerm> sum))) {
                        return new Attempt.NotApplicable();
                    }
                    total = sum;
                }
                tellAnIntTotal(call, total,
                        IntStream.range(from, told.operations.size()).boxed().toList());
                return new Attempt.Form(total);
            }

            /**
             * What a walk from a seed over a container of the input comes to, where its step
             * written at the call only adds to the answer so far ({@link InputNumber#ofAWalkAdding}):
             * the seed and the total of what the step adds. The number is the walk's, and what a
             * run gets past is asked of the walk and not of the total: the step works out an
             * {@code Int} answer at every element, which a sum holds to the type only at its end.
             * Where every number on the way is shown to lie between nought and the answer
             * ({@link NumbersOnTheWayToATotal}), a run stops only where the answer has no place,
             * which is told as the one operation it is; otherwise not every operation is told.
             */
            private LinearForm<NumericTerm> walkAddingOverAContainer(Core node, InputReads at) {
                InputNumber.SeedAndAdded walk = InputNumber.ofAWalkAdding(node, inputs, at,
                        ruleSource, closure -> Core.withoutStanding(closure)
                                instanceof Core.Block block ? block : null);
                if (walk == null) {
                    walk = InputNumber.ofAWalkJoiningTwoMaps(node, inputs, at, ruleSource,
                            closure -> Core.withoutStanding(closure)
                                    instanceof Core.Block block ? block : null);
                }
                if (walk == null) {
                    return null;
                }
                LinearForm<NumericTerm> answer = new LinearForm<>(walk.seed(),
                        walk.added().coefs());
                named.addAll(answer.coefs().keySet());
                if (NumbersOnTheWayToATotal.completeWhereTheAnswerHasAPlace(node, answer,
                        ofTheInput, at)) {
                    tellAnIntTotal(node, answer, List.of());
                } else {
                    NumericTerm total = addedAsItIs(walk.added());
                    if (total == null || !onlyAddsTheElement(node, total)) {
                        told.exact = false;
                    } else {
                        tellAnIntTotal(node, answer, List.of());
                        told.partials.add(total);
                    }
                }
                told.readByATerm(node);
                return answer;
            }

            /**
             * Whether {@code node}, a number rounded to a whole one the way its policy says, is
             * worked out here and stops no run beyond what is told of the number before rounding:
             * that number is read as any is, its operations told, and rounding keeps the order of
             * the numbers, so the rounded number lies from what the least of the number rounds to,
             * to what the greatest does. A run stops at the rounding only where that is past the
             * ends of an {@code Int}, so it stops at none where the range lies within them, and the
             * range is what is known of the rounded number from here on.
             *
             * <p>False where the call is no such rounding, its policy is not written out, or the
             * range is not known to lie inside the ends of an {@code Int}.
             */
            private boolean roundingWorkedOut(Core node, InputReads at,
                                              StoppedValues.Held aside) {
                RoundedToAWholeNumber.Written rounding = RoundedToAWholeNumber.written(node,
                        policy -> WrittenOutElements.reading(ruleSource.symbols(),
                                ruleSource.newtypes()).standing(policy, at).value());
                if (rounding == null || !(AffineForms.outcome(rounding.value(), at, this)
                        instanceof AffineForms.Outcome.Composed<NumericTerm, InputReads> number)) {
                    return false;
                }
                FormRange before =
                        FormRange.held(number.form(), stoppedAt.read(), stoppedAt.ranges());
                ExactRatio least = before == null ? null : rounding.roundedFrom(before.least());
                ExactRatio greatest = before == null ? null : rounding.roundedFrom(before.greatest());
                if (least == null || greatest == null) {
                    return false;
                }
                FormRange rounded = new FormRange(least, greatest);
                WhereAnOperatorAnswers.WhereItsExactValueIsHeld ofAnInt =
                        WhereAnOperatorAnswers.WHAT_AN_INT_HOLDS;
                if (!rounded.liesWithin(ofAnInt.least(), ofAnInt.greatest())) {
                    return false;
                }
                aside.rangeIs(rounded);
                return true;
            }

            /**
             * Whether {@code node} is a walk from a written number whose step is the answer so
             * far and what {@code total} adds up of the element, written as that and no more: the
             * element itself for a total of the elements, the product of fields of it for a
             * total of products. The reading composes a step as a form, which leaves out the
             * operations that were written to get to it, and an operation not written is one no
             * run can stop at.
             */
            private static boolean onlyAddsTheElement(Core node, NumericTerm total) {
                // The walk joining two maps is read only of the one step, which adds the product
                // as it is written ({@link InputNumber#ofAWalkJoiningTwoMaps}).
                if (total instanceof NumericTerm.TakenOver over
                        && over.source() instanceof RunSource.JoinedOccurrences) {
                    return true;
                }
                SeededWalk walk = SeededWalk.of(node, closure -> Core.withoutStanding(closure)
                        instanceof Core.Block block ? block : null);
                if (walk == null || !(Core.withoutStanding(walk.seed()) instanceof Core.Int)
                        || !(Core.withoutStanding(walk.step().body())
                                instanceof Core.Binary sum) || sum.op() != BinOp.ADD) {
                    return false;
                }
                BindingId carried = walk.accumulator().binding();
                BindingId element = walk.element().binding();
                return (isRead(sum.left(), carried) && writtenAs(sum.right(), element, total))
                        || (isRead(sum.right(), carried) && writtenAs(sum.left(), element, total));
            }

            private static boolean isRead(Core e, BindingId name) {
                return Core.withoutStanding(e) instanceof Core.Read read
                        && name.equals(read.binding());
            }

            /**
             * Whether {@code e} is what {@code total} adds up of the element {@code element}, as
             * it is written: the element, or a product of fields of it.
             */
            private static boolean writtenAs(Core e, BindingId element, NumericTerm total) {
                return total instanceof NumericTerm.TakenOf ? isRead(e, element)
                        : multipliesFieldsOf(e, element);
            }

            /** Whether {@code e} is fields of {@code element} multiplied, and nothing else. */
            private static boolean multipliesFieldsOf(Core e, BindingId element) {
                Core here = Core.withoutStanding(e);
                if (here instanceof Core.Binary product && product.op() == BinOp.MUL
                        && product.type() == Type.INT) {
                    return multipliesFieldsOf(product.left(), element)
                            && multipliesFieldsOf(product.right(), element);
                }
                while (true) {
                    switch (here) {
                        case Core.Read read -> {
                            return element.equals(read.binding());
                        }
                        case Core.FieldAccess access -> here = Core.withoutStanding(access.target());
                        case Core.FieldProjection projection ->
                                here = Core.withoutStanding(projection.base());
                        default -> {
                            return false;
                        }
                    }
                }
            }

            /**
             * The total of a container's elements that {@code added} is, where a walk adds each
             * element as it stands, or the product of fields of it, and nothing else — or null
             * where it adds anything beside that. Nothing is then worked out of an element before
             * it is added, so the one thing a run can stop at besides the answer is a running
             * total.
             */
            private static NumericTerm addedAsItIs(LinearForm<NumericTerm> added) {
                if (added.coefs().size() != 1 || !added.constant().isZero()) {
                    return null;
                }
                Map.Entry<NumericTerm, ExactRatio> only = added.coefs().entrySet().iterator().next();
                return ExactRatio.ONE.equals(only.getValue()) && isATotalOfProductsOrElements(
                        only.getKey()) ? only.getKey() : null;
            }

            /** Whether {@code term} adds up the elements of a container, or one product of fields
             *  of each element at the weight one. */
            private static boolean isATotalOfProductsOrElements(NumericTerm term) {
                return switch (term) {
                    case NumericTerm.TakenOf taken ->
                            taken.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
                    case NumericTerm.TakenOver over -> aProductOfFieldsPerElement(over);
                    default -> false;
                };
            }

            /** Whether {@code over} adds up, over the elements of a container, one product of at
             *  least two fields of each at the weight one. */
            private static boolean aProductOfFieldsPerElement(NumericTerm.TakenOver over) {
                if (over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                        && over.source() instanceof RunSource.JoinedOccurrences) {
                    return true;
                }
                if (!(over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds)
                        || !(over.source() instanceof RunSource.ComputedOccurrences computed)
                        || !(computed.computation() instanceof ElementValue.Multilinear product)
                        || !product.form().constant().isZero()
                        || product.form().coefs().size() != 1) {
                    return false;
                }
                Map.Entry<ElementValue.Monomial, ExactRatio> only =
                        product.form().coefs().entrySet().iterator().next();
                return ExactRatio.ONE.equals(only.getValue()) && only.getKey().rounding() == null
                        && only.getKey().fields().size() >= 2;
            }

            /**
             * Whether {@code node} is the total of a closure's answers over a container, the
             * closure a product of fields of the element and nothing else, as {@code total} is
             * read: {@code List.sum(List.map(l -> l.price * l.qty, lines))}.
             */
            private static boolean sumsProductsOfFields(Core node, NumericTerm total) {
                if (!aProductOfFieldsPerElement((NumericTerm.TakenOver) total)
                        || !(Core.withoutStanding(node) instanceof Core.PreservedCall sum)
                        || sum.args().size() != 1
                        || !(Core.withoutStanding(sum.args().getFirst())
                                instanceof Core.PreservedCall map)) {
                    return false;
                }
                BuiltFrom<DeclaredArgument> built =
                        DefaultBoundOperationFacts.get().buildsItsResultFrom(map.operation());
                DeclaredArgument mapped = built == null ? null : built.mapsEachElementOf();
                int over = mapped == null ? -1 : CallArguments.positionOf(mapped, map.operation());
                if (over < 0 || over >= map.args().size() || map.args().size() != 2) {
                    return false;
                }
                Core closure = Core.withoutStanding(map.args().get(1 - over));
                return closure instanceof Core.Block block && block.params().size() == 1
                        && block.params().getFirst() != null
                        && block.params().getFirst().binding() != null
                        && multipliesFieldsOf(block.body(),
                                block.params().getFirst().binding());
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
                ValueStanding.ReadThrough<InputReads> as = NameAnswers.taken(node, at);
                return as != null || !at.isInsideAnApplicationOverCodePoints() ? as
                        : NameAnswers.armOfAMatchOnAFoundElement(node, at, ruleSource.symbols(),
                                ruleSource.newtypes(), reached);
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

    /**
     * An operation of whole numbers over the expression a reading stopped at, held aside: the
     * form, over the atom the expression is held as; where a run stops at it; and the node that
     * works it out after the operations {@code after}.
     */
    private record SumOverTheStop(Core node, LinearForm<NumericTerm> form,
                                  StoppedValues.Held over, BigInteger least, BigInteger greatest,
                                  List<Integer> after) {

        /** The same operation over {@code bound}, the value the expression held aside is, and
         *  the input's numbers. */
        UndividedByARelation.IntOperation over(UndividedByARelation.IntOperand.OfABinding bound) {
            return new UndividedByARelation.IntOperation(form.over(atom -> LinearForm.atom(
                    atom.equals(over.atom) ? bound
                            : new UndividedByARelation.IntOperand.OfTheInput(atom))),
                    least, greatest, after);
        }

        /**
         * Whether the expression held aside is a bound value, and then this told to {@code told}
         * as the operation over that value it is, unless no value it takes stops a row. The sizes
         * of a form's addends say nothing of a value the comparison was not read as.
         */
        boolean toldOverItsValue(WhatWasTold told, InputReading ofTheInput) {
            if (over.bound == null) {
                return false;
            }
            UndividedByARelation.IntOperation operation = over(over.bound);
            if (!UndividedByARelation.stopsNoRow(operation, ofTheInput)) {
                told.add(node, operation);
            }
            return true;
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
        /** The operations over a stopped value that are told of nowhere, to be asked of the form
         *  of the comparison. */
        private final List<SumOverTheStop> sumsOverTheStop = new ArrayList<>();
        /** The counts of a list whose working out is answered for only where the line the
         *  comparison draws on the count is at a count a list holds, to be asked of the form of
         *  the comparison. */
        private final List<NumericTerm> countsOverTheStop = new ArrayList<>();
        /** The last operation told before the step of a walk being unrolled, by the accumulator
         *  that step reads the answer so far on: what the steps before worked out. */
        private final Map<BindingId, Integer> carriedAfter = new HashMap<>();
        /** The names read under a node read as numbers of the input, where what each was given
         *  was asked with the node ({@link NumbersOnTheWayToATotal}). */
        private final Set<BindingId> readByATerm = new HashSet<>();
        /** How many elements the reading of the comparison has read a closure applied to one by
         *  one, shared with every reading tried apart from it ({@link #apart}). */
        private final int[] elementsRead;
        private boolean exact = true;
        /** Whether a product of two non-constant numbers is a stop and not a number of its own. */
        private boolean productsStop;
        /** The totals of a container whose walk's running totals are the only thing left untold
         *  ({@link UndividedByARelation.Working#partials}). */
        private final List<NumericTerm> partials = new ArrayList<>();
        /** What readings of parts of the comparison tried on their own were told and left to a
         *  witness, in the order they were read ({@link #leftToTheWitness}). */
        private final List<WhatWasTold> leftToTheWitness = new ArrayList<>();
        /** What readings of parts of the comparison tried on their own were told where nothing
         *  says a row is made, in the order they were read ({@link #besideTheRows}). */
        private final List<WhatWasTold> besideTheRows = new ArrayList<>();

        WhatWasTold() {
            this(new int[1]);
        }

        private WhatWasTold(int[] elementsRead) {
            this.elementsRead = elementsRead;
        }

        /** Nothing told yet, for a part of the comparison read apart: what it reads element by
         *  element is counted with what this reading has. */
        WhatWasTold apart() {
            WhatWasTold apart = new WhatWasTold(elementsRead);
            apart.productsStop = productsStop;
            return apart;
        }

        /**
         * The figure a list of {@code elements} is past, or none where it is read element by
         * element, which is counted then: each element is a reading of the condition, no more of
         * them in one list than {@link CompositionBudget#READINGS_OF_ONE_CONDITION} allows, nor in
         * all, along every walk and total read so and inside one another, than
         * {@link CompositionBudget#TOTAL_READINGS_OF_ONE_CONDITION} does. Past either the list is
         * not read so, and what is worked out over it is not told.
         *
         * <p>The check and the reason for passing it are made here and nowhere else, so a reader
         * of the answer has the figure with the refusal.
         */
        Optional<WhyUnread> declinedAtCounting(int elements) {
            if (elements > CompositionBudget.READINGS_OF_ONE_CONDITION.maximum()) {
                return Optional.of(WhyUnread.PAST_THE_READINGS);
            }
            if (elementsRead[0] + elements
                    > CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.maximum()) {
                return Optional.of(WhyUnread.PAST_THE_TOTAL_READINGS);
            }
            elementsRead[0] += elements;
            return Optional.empty();
        }

        /** That {@code node} was read as numbers of the input, with what each name under it was
         *  given. */
        void readByATerm(Core node) {
            Core here = Core.withoutStanding(node);
            if (here instanceof Core.Read name) {
                readByATerm.add(name.binding());
            }
            Core.forEachChild(here, this::readByATerm);
        }

        /** Whether what {@code name} was given was asked with a node read as numbers of the
         *  input. */
        boolean readByATerm(BindingId name) {
            return readByATerm.contains(name);
        }

        void add(Core node, UndividedByARelation.IntOperation operation) {
            at.add(Core.withoutStanding(node));
            operations.add(operation);
        }

        /**
         * What {@code apart}, a reading of part of the comparison tried on its own, was told,
         * taken as told here after everything told so far: each operation and each of decimals
         * moved past the ones already here, with what it was worked out of moved with it, and the
         * forms it knows the operation or the place of carried over to where they now stand.
         */
        void absorb(WhatWasTold apart) {
            int ofWholeNumbers = operations.size();
            for (int i = 0; i < apart.operations.size(); i++) {
                add(apart.at.get(i), apart.operations.get(i).shifted(ofWholeNumbers));
            }
            int ofDecimals = decimals.size();
            for (DecimalOperation each : apart.decimals) {
                decimals.add(each.shifted(ofDecimals));
            }
            apart.resultOf.forEach((form, where) -> resultOf.put(form, where + ofDecimals));
            inputReads.addAll(apart.inputReads);
            sumsOverTheStop.addAll(apart.sumsOverTheStop);
            countsOverTheStop.addAll(apart.countsOverTheStop);
            readByATerm.addAll(apart.readByATerm);
            leftToTheWitness.addAll(apart.leftToTheWitness);
            besideTheRows.addAll(apart.besideTheRows);
            exact &= apart.exact;
            partials.addAll(apart.partials);
        }

        /**
         * That a run works out what {@code apart} was told, and that none of it is told here: the
         * analysis that drew the lines answers for it with a witness that keeps it within its
         * type. It is worked out on every run all the same ({@link #everyOperation}).
         */
        void leftToTheWitness(WhatWasTold apart) {
            leftToTheWitness.add(apart);
        }

        /**
         * That a run works out what {@code apart} was told, and that nothing says a row of a line
         * is made where it is: none of it is told here, and what is told here is then not every
         * operation a row gets past. It is part of where a run stops all the same
         * ({@link #everyOperation}).
         */
        void besideTheRows(WhatWasTold apart) {
            besideTheRows.add(apart);
        }

        /**
         * Every operation a run works out, as {@link #working} tells it with the operations left to
         * a witness and those told beside the rows after it: those are no part of what a row of a
         * line gets past, and are part of where a run stops ({@link StopEvidence}). Each group
         * keeps what its operations were worked out of among themselves; of the rest nothing is
         * said, so each operation told is taken as one a run may work out first. Every one is
         * told where nothing else is left untold, whether or not a row is shown to be made.
         *
         * @param onEveryRun whether every run getting to the comparison works all of them out
         */
        UndividedByARelation.Working everyOperation(boolean onEveryRun) {
            List<UndividedByARelation.IntOperation> every = new ArrayList<>(operations);
            List<WhatWasTold> groups = new ArrayList<>(leftToTheWitness);
            groups.addAll(besideTheRows);
            for (WhatWasTold group : groups) {
                UndividedByARelation.Working worked = group.everyOperation(true);
                int before = every.size();
                worked.operations().forEach(each -> every.add(each.shifted(before)));
            }
            UndividedByARelation.Working out = working(every, exact && partials.isEmpty());
            return onEveryRun ? out : out.notOnEveryRun();
        }

        /**
         * That the step about to be read is handed the answer so far on {@code accumulator}, so
         * what it works out of that is worked out after every operation told so far: the seed's,
         * the elements', and the steps before.
         */
        void after(BindingId accumulator) {
            if (operations.isEmpty()) {
                carriedAfter.remove(accumulator);
            } else {
                carriedAfter.put(accumulator, operations.size() - 1);
            }
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
                case Core.Construct construct when !construct.values().isEmpty() ->
                        List.of(construct.values().get(0).value());
                default -> List.<Core>of();
            });
        }

        /** The same, of a node worked out of {@code operands}. */
        List<Integer> workedOutOf(List<Core> operands) {
            List<Integer> out = new ArrayList<>();
            for (Core operand : operands) {
                Core bare = Core.withoutStanding(operand);
                if (bare instanceof Core.Read name
                        && carriedAfter.get(name.binding()) instanceof Integer last) {
                    out.add(last);
                    out.addAll(operations.get(last).after());
                    continue;
                }
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
            NumericTerm total = bare.type() == Type.DECIMAL ? aPlainTotal(form) : null;
            return total == null ? null : new DecimalOperation.Total(total);
        }

        /** The term {@code form} is, where it is the total of the decimals a container holds or
         *  of one path inside each element, added as they are; null where it is anything else.
         *  The scale of such a total is that of the elements, which a row writes at the places of
         *  the total: a total of products has the sum of the scales of their factors, which
         *  {@link DecimalOperation.Total} does not bound. */
        private static NumericTerm aPlainTotal(LinearForm<NumericTerm> form) {
            if (form.coefs().size() != 1 || !form.constant().isZero()) {
                return null;
            }
            Map.Entry<NumericTerm, ExactRatio> only = form.coefs().entrySet().iterator().next();
            boolean added = ExactRatio.ONE.equals(only.getValue()) && switch (only.getKey()) {
                case NumericTerm.TakenOf taken ->
                        taken.takenAs() instanceof TakenAs.TheSumOfWhatItHolds;
                case NumericTerm.TakenOver over ->
                        over.takenAs() instanceof TakenAs.TheSumOfWhatItHolds
                                && over.source() instanceof RunSource.ProjectedOccurrences;
                default -> false;
            };
            return added ? only.getKey() : null;
        }

        /** That {@code form} is the number a row holds at a place of the input, read as it is. */
        void readsTheInput(LinearForm<NumericTerm> form) {
            inputReads.add(form);
        }


        /** What a row of a line gets past: not every operation where some were told beside the
         *  rows, since nothing says a row is made where those are worked out. */
        UndividedByARelation.Working working() {
            return working(operations, exact && partials.isEmpty() && besideTheRows.isEmpty());
        }

        private UndividedByARelation.Working working(
                List<UndividedByARelation.IntOperation> told, boolean everyOne) {
            return new UndividedByARelation.Working(told, everyOne
                    ? WhatARelationLeavesUndivided.Told.EVERY
                    : WhatARelationLeavesUndivided.Told.SOME,
                    true, decimals, exact ? partials : List.of());
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
                        WorkedOutToReachIt.of(ofTheInput)
                                .endsNoRun(new Denotation(only.expression(), at))
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
        if (WorkedOutToReachIt.of(ofTheInput).endsNoRun(new Denotation(expression, at))) {
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
                    instanceof AffineForms.Outcome.StoppedAt<NumericTerm, InputReads>
                    && !isARemainderOfAReadForm(side, at, reading, ofTheInput.rules(),
                            WorkedOutToReachIt.of(ofTheInput))) {
                told.exact = false;
            }
        }
        return told.working();
    }

    /**
     * Whether {@code side} is a floor remainder by a positive constant and the number it takes the
     * remainder of reads as a form. Working it out runs nothing but the number it divides, whose
     * operations are told as that is read, and the remainder is not an operation a run stops at.
     *
     * <p>That the divisor comes to a positive number is a question of values. What is worked out
     * to reach the divisor, and whatever else {@code side} is written with, is asked of
     * {@code side} as it is written, apart from the dividend and the remainder itself.
     */
    private static boolean isARemainderOfAReadForm(
            Core side, InputReads reads, AffineForms.Reading<NumericTerm, InputReads> reading,
            RuleReadingSource rules, WorkedOutToReachIt reached) {
        Denotation standing = reads.standing(side, rules.symbols(), rules.newtypes());
        InputReads at = standing.at();
        if (!(Core.withoutStanding(standing.value()) instanceof Core.PreservedCall call)) {
            return false;
        }
        OptionalInt divisor = DefaultBoundOperationFacts.get()
                .divisorOfAFloorRemainder(call.operation());
        if (divisor.isEmpty() || call.args().size() != 2) {
            return false;
        }
        int dividend = 1 - divisor.getAsInt();
        return at.folded(call.args().get(divisor.getAsInt()), rules.symbols(), rules.newtypes())
                        .orElse(null) instanceof Long by && by > 0
                && AffineForms.outcome(call.args().get(dividend), at, reading)
                        instanceof AffineForms.Outcome.Composed<NumericTerm, InputReads>
                && reached.besideWhatWasRestated(List.of(call.args().get(dividend)), call)
                        .endsNoRun(new Denotation(side, reads));
    }

    /** Whether what {@code expression} works out ends no run, apart from the closures
     *  {@code told}, whose bodies are read of their own. A closure written anywhere else in it is
     *  applied by the call it is written at, and where that stops is no one's but that closure's. */
    private static boolean restEndsNoRun(Core expression, InputReads at,
                                         WorkedOutToReachIt reached, List<Denotation> told) {
        Core here = Core.withoutStanding(expression);
        if (!(here instanceof Core.PreservedCall call)
                || !WhatARunMayEndFor.itselfApartFromTheClosuresWrittenAtIt(call).endsNone()) {
            return reached.endsNoRun(new Denotation(expression, at));
        }
        for (Core argument : call.args()) {
            boolean ends = Core.withoutStanding(argument) instanceof Core.Block closure
                    ? isTold(closure, told)
                    : restEndsNoRun(argument, at, reached, told);
            if (!ends) {
                return false;
            }
        }
        return true;
    }

    private static boolean isTold(Core.Block closure, List<Denotation> told) {
        Core body = Core.withoutStanding(closure.body());
        return told.stream().anyMatch(each -> Core.withoutStanding(each.value()) == body);
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
     * What the analysis that drew the lines answers for of the expressions held aside beside a
     * stop, the stopped one among them: those it reads the comparison again with each value of
     * ({@code readAgain}), which tells what working that value out does; and those it reads as
     * the form of one of their operands ({@code readByTheFormOf} answers that operand), whose rows
     * it builds where that form is worked out, which is all working the operand out does where
     * every operation on the way adds up addends of the form. Those it reads as a remainder whose
     * rows it does not say are made where the dividend is worked out ({@code dividendBesideTheRows}
     * answers the dividend): a remainder of a dividend over a bound value, and one of a place
     * moved by a number, read as the place's own. What a run stops at in working the dividend out
     * is told for where a run stops, and is nothing a row gets past. And
     * the value it reads an expression held aside as, where that is the value of a name
     * ({@code boundAs}, null where it is not): an operation over it is one over that value, which
     * a relation over the value is asked to get past.
     */
    record WhatTheAnalysisAnswersFor(Predicate<Core> readAgain,
                                     Function<Core, Core> readByTheFormOf,
                                     Function<Core, Core> dividendBesideTheRows,
                                     BiFunction<Core, InputReads, Quantity.OfABinding> boundAs) {

        static final WhatTheAnalysisAnswersFor NOTHING =
                new WhatTheAnalysisAnswersFor(_ -> false, _ -> null, _ -> null, (_, _) -> null);

        WhatTheAnalysisAnswersFor {
            Objects.requireNonNull(readAgain);
            Objects.requireNonNull(readByTheFormOf);
            Objects.requireNonNull(dividendBesideTheRows);
            Objects.requireNonNull(boundAs);
        }

        static WhatTheAnalysisAnswersFor readingAgain(Predicate<Core> readAgain) {
            return new WhatTheAnalysisAnswersFor(readAgain, _ -> null, _ -> null, (_, _) -> null);
        }
    }

    /**
     * What one reading of a comparison tells of what is worked out on the way to its answer, for
     * the two things that are asked of it.
     *
     * @param toGetPast what a row of a line the comparison draws is asked to get past
     * @param stops     what a run getting to the comparison works out, for where a run stops in it
     */
    record WorkedOut(UndividedByARelation.Working toGetPast, StopEvidence stops) {

        WorkedOut {
            Objects.requireNonNull(toGetPast, "what a row gets past, or that it is not known");
            Objects.requireNonNull(stops, "what a run works out, or that it is not known");
        }

        /** Of a reading that leaves nothing to a witness: a run works out what a row gets past. */
        static WorkedOut ofWhatIsToldOf(UndividedByARelation.Working working) {
            return new WorkedOut(working, StopEvidence.ofWhatIsToldOf(working));
        }
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
        private final WhatTheAnalysisAnswersFor answersFor;
        private final Map<Core, Held> byExpression = new IdentityHashMap<>();
        private final Map<NumericTerm, Held> byAtom = new LinkedHashMap<>();
        private Held theStop;
        private boolean stopWorksOutItsForm;

        StoppedValues(Core stop, boolean quotientAwayFromNought, InputReading read,
                      WhatTheAnalysisAnswersFor answersFor) {
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
            /** The bound value the derivation reads the expression as, where an operation of
             *  whole numbers can be over it; null otherwise. */
            private UndividedByARelation.IntOperand.OfABinding bound;

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

            void boundIs(UndividedByARelation.IntOperand.OfABinding bound) {
                this.bound = bound;
            }
        }

        /**
         * The bound value the analysis that drew the lines reads {@code expression}, read in
         * {@code at}, as, where the expression is a name read and an operation of whole numbers
         * can be over its value ({@link UndividedByARelation.IntOperand.OfABinding#isOne}); null
         * otherwise.
         */
        UndividedByARelation.IntOperand.OfABinding boundAs(Core expression, InputReads at) {
            if (!(Core.withoutStanding(expression) instanceof Core.Read name)) {
                return null;
            }
            Quantity.OfABinding bound = answersFor.boundAs().apply(expression, at);
            return bound != null && UndividedByARelation.IntOperand.OfABinding.isOne(bound)
                    ? new UndividedByARelation.IntOperand.OfABinding(bound, name.name()) : null;
        }

        /** Whether the expression the reading stopped at was met and is a bound value: reading a
         *  name works nothing out, and ends no run before the operations told. */
        boolean theStopIsABoundValue() {
            return theStop != null && theStop.met && theStop.bound != null;
        }

        /** That working {@code node} out adds up the form of one operand of it and ends a run
         *  nowhere else ({@link #theStopWorksOutTheFormItIsReadAs}). */
        void worksOutTheFormItIsReadAs(Core node) {
            if (stop.equals(node)) {
                stopWorksOutItsForm = true;
            }
        }

        /** Whether working the expression the reading stopped at out is adding up the form of one
         *  operand of it and nothing else that ends a run: those sums come before what it makes
         *  of them, so a run getting to it works every one of them out. */
        boolean theStopWorksOutTheFormItIsReadAs() {
            return stopWorksOutItsForm;
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

        /** Whether the analysis that drew the lines answers for what working {@code held}, an
         *  expression held aside, may stop a run at: it reads the comparison again with each
         *  value the expression may come to, which tells what working that value out does. */
        boolean answersFor(Core held) {
            return answersFor.readAgain().test(held);
        }

        /** The operand of {@code held} whose form the analysis that drew the lines reads it as,
         *  or null where it reads it so by none. */
        Core readByTheFormOf(Core held) {
            return answersFor.readByTheFormOf().apply(held);
        }

        /** The dividend of the remainder the analysis that drew the lines reads {@code held} as,
         *  where it does not say a row is made where the dividend is worked out; null where it
         *  reads it as none such. */
        Core dividendBesideTheRows(Core held) {
            return answersFor.dividendBesideTheRows().apply(held);
        }

        /** The same reading, holding {@code value} aside as the expression it stopped at: a name
         *  read whose value is a bound value. */
        StoppedValues heldAt(Core value) {
            return new StoppedValues(value, false, read, answersFor);
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
        UndividedByARelation.Working apart(WhatTheAnalysisAnswersFor answersFor) {
            return worksOut(answersFor).toGetPast();
        }

        /**
         * The same, with what a run getting to the comparison works out, read off the one reading:
         * the operations left to a witness as well, which a run works out all the same.
         */
        WorkedOut worksOut(WhatTheAnalysisAnswersFor answersFor) {
            WorkedOut beside = beside(new StoppedValues(node, false, ofTheInput, answersFor));
            return beside.toGetPast().operations().isEmpty() && beside.toGetPast().exact()
                    ? new WorkedOut(UndividedByARelation.Working.NOTHING, beside.stops())
                    : beside;
        }

        /** The same for the quotient {@code division}, which the analysis answers for with
         *  everything written under it and under the expression the reading stopped at, which it
         *  reads the quotient out of. */
        UndividedByARelation.Working ofTheQuotientAwayFromNought(Core division) {
            Set<Core> under = Collections.newSetFromMap(new IdentityHashMap<>());
            collectUnder(division, under);
            collectUnder(node, under);
            return beside(new StoppedValues(division, true, ofTheInput,
                    WhatTheAnalysisAnswersFor.readingAgain(
                            node -> under.contains(Core.withoutStanding(node))))).toGetPast();
        }

        private static void collectUnder(Core around, Set<Core> into) {
            Core here = Core.withoutStanding(around);
            into.add(here);
            Core.forEachChild(here, child -> collectUnder(child, into));
        }

        /**
         * Whether the comparison {@code whole} is a cut of draws its line on {@code count} alone,
         * at a count a list holds: the form is the count and nothing else, so the line is one
         * count whatever the rest of the input is, and that count and the one above it are
         * counts of a list, the whole numbers up to {@code Integer.MAX_VALUE}. The rows on the
         * line then hold lists a run can make. {@code List.length(found) + 100 >= 1} is a line at
         * a count below nought, which no list is at.
         */
        static boolean lineIsAtACountAListHolds(LinearForm<NumericTerm> whole,
                                                NumericTerm count) {
            if (whole == null || whole.coefs().size() != 1
                    || !whole.coefs().containsKey(count)) {
                return false;
            }
            return whole.constant().negated().dividedBy(whole.coefs().get(count)).orNull()
                    instanceof ExactRatio line && line.isWhole()
                    && line.signum() >= 0
                    && line.compareTo(ExactRatio.of(Integer.MAX_VALUE)) < 0;
        }

        private WorkedOut beside(StoppedValues stoppedAt) {
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
            for (SumOverTheStop sum : told.sumsOverTheStop) {
                // An operation over a bound value is one over that value, which a relation over
                // it is asked to get past.
                if (!sum.toldOverItsValue(told, ofTheInput) && !areAddendsOf(sum.form(), whole)) {
                    told.exact = false;
                }
            }
            for (NumericTerm count : told.countsOverTheStop) {
                if (!lineIsAtACountAListHolds(whole, count)) {
                    told.exact = false;
                }
            }
            // The stopped expression is worked out too, and a run may stop in it before any
            // operation told — unless it is a name read, which works nothing out. Where all it
            // works out is the form it is read by, those sums are what a run stops in there, and
            // a run getting to the comparison works every one out; what a row of a line gets past
            // is still not every one, since the sums left to a witness are not among them.
            boolean aName = stoppedAt.theStopIsABoundValue();
            return new WorkedOut(aName ? told.working() : told.working().notOnEveryRun(),
                    new StopEvidence(told.everyOperation(
                            aName || stoppedAt.theStopWorksOutTheFormItIsReadAs())));
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
            if (here == null || here.answered() == null || !here.answered().counts()) {
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
