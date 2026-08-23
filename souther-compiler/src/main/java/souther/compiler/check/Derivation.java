package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.List;

/**
 * How a value the affine fragment cannot carry was computed from values it can.
 *
 * <p>What is recorded here is the construction's own meaning and nothing the path says. The same
 * expression is read more than once — under what the guards established, and under what holds of the
 * values whatever the guards did — and a fact that depends on which reading is asking belongs to the
 * reading and not to this. So a recipe states what was computed and what the operator is, and
 * everything about where the operands lie is applied where the recipe is read
 * ({@link DerivedNumericFacts}).
 *
 * <p>That is not a rule against choosing here. Which operators have a recipe at all is a question
 * about the operator and not about the path — {@code /} on {@code Decimal} rounds at a precision the
 * run time sets and has none for that reason — and choices of that kind are made where the recipe is
 * recorded ({@link Terms}).
 */
sealed interface Derivation {

    /**
     * The forms this recipe is read from.
     *
     * <p>Answered by the recipe and not worked out from its shape. What a recipe is read from is not
     * the same question as what it is arithmetic over, and the two look alike only while every
     * recipe is arithmetic: a product's operands are both, and a choice's arms are read from without
     * being arithmetic over anything, and what chose between them would be read from without even
     * standing in the answer. A reader that decided the question by looking at which components
     * happen to be forms would be answering a semantic question by a naming convention, and would
     * miss the first one that arrives inside something else.
     *
     * <p>What it is for is {@link Terms#reached}, which is what says which places a form is about.
     * {@link StepInputFacts} keeps only the places a step names, so a form a recipe is read from and
     * that walk does not reach leaves those places unbounded — and nothing else says so.
     *
     * <p>Abstract, so that a recipe added later is asked this before it compiles.
     */
    List<LinearForm<FactSubject>> formsRead();

    /**
     * Every value the operator's divisor can take, or null where the recipe divides by nothing.
     *
     * <p>The one part of a recipe that is not a form, and here for the reason {@link #formsRead} is:
     * whether two readings computed a value the same way is a question about every recipe there is,
     * and asked by switching on the kind it is a place a recipe added later is silently left out of.
     * Answered by the recipe, so that the reader comparing two of them has every part of both.
     */
    NumericDomain.Bounds divisorExtent();

    /**
     * The relations this recipe states, in the order it states them, or an empty list where it
     * states none.
     *
     * <p>Beside {@link #formsRead} and {@link #divisorExtent} for the reason those are answered by
     * the recipe: whether two readings computed a value the same way is a question about every
     * recipe there is, and a part of one that no reader can ask about is a part two readings may
     * differ in while being taken for one. A choice records what choosing each arm states
     * ({@link Chosen.Arm#settles}), and the relation in one of those is not a form, so without this
     * two conditions over the same values and opposite comparisons would be one recipe.
     *
     * <p>The forms those relations are written over are {@link #formsRead}'s to answer, which is a
     * different question: what the reading reaches, rather than what tells two recipes apart.
     */
    List<Rel> relationsRead();

    record Product(LinearForm<FactSubject> left, LinearForm<FactSubject> right) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return List.of(left, right);
        }

        /** It states no relation: what it is, is arithmetic over its forms. */
        @Override
        public List<Rel> relationsRead() {
            return List.of();
        }

        @Override
        public NumericDomain.Bounds divisorExtent() {
            return null;
        }
    }

    /**
     * A value that is one of several: an {@code if}, a {@code match}, and anything else that answers
     * one of the values standing in it.
     *
     * <p>Not arithmetic, and here beside the arithmetic for the reason this interface gives: what is
     * recorded is how a value was computed, and being one of several is a way of computing one. The
     * affine walk already names such a node — a choice is one value, and a rule written about it is
     * about the thing that stands there — and until this arm existed nothing was filed under that
     * name, so the value came out with no range whatever its arms answered.
     *
     * <p>Each arm is read in the environment choosing it puts the reading in, so an arm's body
     * reading what the arm bound is read: {@code | Held as h -> a + h.amount.value} names a value
     * only that arm has, and it is entered before the arm is named ({@link Terms#choosing}).
     *
     * <p>What choosing an arm states stands beside it, as relations ({@link Chosen.Arm#settles}).
     * That is not a range and not what the path assumed: {@code x < 100} is the same statement
     * wherever it is read, and what it comes to is the answer of whichever domain it is taken into.
     * So the relation is recorded and its consequence is not ({@link DerivedBounds}).
     *
     * <p>Recorded and not looked up later, because what a reading may reach is decided now:
     * {@link StepInputFacts} keeps the places a step names, so a value an arm is read under that
     * this does not list arrives at that reading with its guarantee already dropped.
     *
     * <p>What a case refines the scrutinee to and what an attempt's construction guarantees are not
     * relations a condition wrote but guarantees about a place, and they are read where places are
     * seeded rather than here.
     *
     * <p>The operations the library defines by cases ({@code DischargeRules.CHOOSES}) are choices
     * with no producer here yet (#974). Which values a choice is one of does have an owner
     * ({@link Choice}), so a kind of choice is found by every reader at once or by none.
     *
     * @param arms what stands in each arm, and what reading its context may reach. Every arm or
     *             none: an arm the walk could not read leaves the choice with no recipe at all,
     *             since a range that left one of them out would be a range the value can be outside
     *             of. Never none of them — one of several is what this is, so a producer handing
     *             over an empty list has disagreed with that rather than described a value, and a
     *             reader taking it for a range with no ends would hide the disagreement as a loss of
     *             precision.
     */
    record Chosen(List<Arm> arms) implements Derivation {

        /**
         * One arm of a choice: the value it answers, and what choosing it states.
         *
         * @param answer  what stands in the arm, as a form, read where choosing the arm put the
         *                reading.
         * @param settles the relations choosing this arm states, and only those that hold on their
         *                own ({@link Conditions#settledBy}). Relations and not ranges: what
         *                {@code x < 100} comes to is the domain's answer and the domain's alone,
         *                while what it says is the same wherever it is read, which is why one may
         *                stand here and the other may not.
         */
        record Arm(LinearForm<FactSubject> answer, List<NumericConstraint> settles) {

            public Arm {
                settles = List.copyOf(settles);
            }
        }

        public Chosen {
            arms = List.copyOf(arms);
            if (arms.isEmpty()) {
                throw new IllegalArgumentException("a value that is one of several was recorded with"
                        + " none to be one of");
            }
        }

        /** The arms, and the forms the relations beside them are written over. Both, because a form
         * an arm is read under and this leaves out is a place left unbounded with nothing saying so.
         * The second is the dependency that arrives inside something else, which a reader working
         * the question out from which components happen to be forms would miss. */
        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            List<LinearForm<FactSubject>> out = new java.util.ArrayList<>();
            for (Arm arm : arms) {
                out.add(arm.answer());
                for (NumericConstraint settled : arm.settles()) {
                    out.add(settled.form());
                }
            }
            return List.copyOf(out);
        }

        @Override
        public NumericDomain.Bounds divisorExtent() {
            return null;
        }

        /** The relations the arms state, arm by arm and in order. Without this two choices whose
         * arms are written over the same values and compared the opposite way round answer the same
         * forms, and a reader comparing recipes would take them for one. */
        @Override
        public List<Rel> relationsRead() {
            List<Rel> out = new java.util.ArrayList<>();
            for (Arm arm : arms) {
                for (NumericConstraint settled : arm.settles()) {
                    out.add(settled.rel());
                }
            }
            return List.copyOf(out);
        }
    }

    /**
     * A truncating divide.
     *
     * @param numerator     what is divided.
     * @param divisor       what it is divided by. A form and not a written number: a divisor the
     *                      path bounds away from zero has the sign and the magnitude the rule needs
     *                      as surely as a written one does, and holding it as a number was what left
     *                      every divisor with a coefficient unread.
     * @param divisorExtent every value the operator's divisor can take, which is what its type
     *                      holds. Not a bound the path proves — the arithmetic composed over a form
     *                      runs over numbers of any size, and the operator's divisor is a value of
     *                      its own type, so a range with none of them in it is not a divisor this
     *                      operator has. Read where the recipe is read, and not a fact about any
     *                      path.
     */
    record TruncatingQuotient(LinearForm<FactSubject> numerator, LinearForm<FactSubject> divisor,
                              NumericDomain.Bounds divisorExtent) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return List.of(numerator, divisor);
        }

        /** It states no relation: what it is, is arithmetic over its forms. */
        @Override
        public List<Rel> relationsRead() {
            return List.of();
        }
    }

    /**
     * What that divide leaves of what it divided.
     *
     * <p>The same three parts and for the same reasons, because it is the same division: what is
     * known of a remainder is decided by the sign of what was divided and by how big the divisor is,
     * and both are read where the recipe is read. Held as its own recipe and not as the arithmetic
     * {@code numerator - divisor * quotient} it satisfies: that identity is a fact about the two
     * answers of one division and not a way of computing either, and writing it as one would make
     * what a remainder is depend on {@code /} answering at all — which for one pair of {@code Int}s
     * it does not (spec §stdlib-int).
     */
    record TruncatingRemainder(LinearForm<FactSubject> numerator, LinearForm<FactSubject> divisor,
                               NumericDomain.Bounds divisorExtent) implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return List.of(numerator, divisor);
        }

        /** It states no relation: what it is, is arithmetic over its forms. */
        @Override
        public List<Rel> relationsRead() {
            return List.of();
        }
    }

    /**
     * A divide rounded to a scale the call states (spec §stdlib-decimal).
     *
     * <p>{@code scale} is a form, as the divisor is, and for the same reason: whether it comes to
     * one number is what a reading proves of it, and one expression is read under more than one
     * reading. Held as a written number, this asked the question where the recipe was recorded, so a
     * scale a rule of the model settles — a parameter whose type admits one value, a name a guard
     * equates to two — was a scale no reading could recover. What is stated where a reading has no
     * one number for it is the half that does not need one.
     *
     * <p>The mode is not here at all. Every mode the library has lands the answer on one of the two
     * grid points the exact quotient lies between, so what a range can say is the same for all seven
     * of them ({@link souther.compiler.numeric.Intervals#roundedQuotient}). Which one it is is part
     * of which value this is — {@link NumericMeaning} keeps it — and not part of where it lies.
     */
    record RoundedQuotient(LinearForm<FactSubject> numerator, LinearForm<FactSubject> divisor,
                           NumericDomain.Bounds divisorExtent, LinearForm<FactSubject> scale)
            implements Derivation {

        @Override
        public List<LinearForm<FactSubject>> formsRead() {
            return List.of(numerator, divisor, scale);
        }

        /** It states no relation: what it is, is arithmetic over its forms. */
        @Override
        public List<Rel> relationsRead() {
            return List.of();
        }
    }
}
