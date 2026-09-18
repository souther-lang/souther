package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

/**
 * A condition about an answer that the value standing a dependency in was not composed against, and
 * which stage let it go.
 *
 * <p>The answer side's own account, beside {@link ReachabilityGap} and never one of its shapes.
 * What that one is about is the input a row writes values at; what this is about is the value a row
 * stands a dependency in with, which is a different subject with a different vocabulary for what
 * went wrong. A record compared with another has no order for a region to measure it on, and saying
 * so in the words of a position of the input would name a position no row writes.
 *
 * <p><b>Two stages, for the reason the other side has two.</b> A condition the demand reading has no
 * way of stating never reached a composer; one it stated that no value could be composed against
 * reached one and came back. What a reader does about them differs — write the condition another
 * way, or wait for this compiler to gain a way of building the value — and a single word for both
 * would send an author after whichever of the two somebody happened to be looking at.
 *
 * <p>Nothing here says a value does not exist. Each entry says what this compiler did, and a word
 * going away is a capability gained.
 */
public sealed interface DemandGap {

    /** Which question a report about the condition asks for its place. */
    ConditionReportAnchor anchor();

    /**
     * The demand reading had no way of stating it, so nothing was composed against it.
     *
     * <p>Carrying the anchor and not a demand, because there is no demand: what the reading came to
     * is that this condition asks something of an answer that it cannot put to a composer. The
     * reason is what tells two of them apart, and the anchor is where a reader is sent.
     */
    record Unstated(ConditionReportAnchor anchor, WhyNotStated why) implements DemandGap {

        public Unstated {
            if (anchor == null || why == null) {
                throw new IllegalArgumentException(
                        "a demand this reading could not state says where and what stopped it");
            }
        }
    }

    /**
     * The reading stated it and nothing composed a value under it.
     *
     * <p>Carrying the demand and not a copy of what it said. A report may say which places of the
     * answer it is over, and a reader asking why no value meets it is asking about that demand.
     */
    record Uncomposed(AnswerDemand demand, WhyNotComposed why) implements DemandGap {

        public Uncomposed {
            if (demand == null || why == null) {
                throw new IllegalArgumentException(
                        "a demand nothing composed under says which demand and what stopped it");
            }
        }

        @Override
        public ConditionReportAnchor anchor() {
            return demand.anchor();
        }
    }

    /**
     * What stopped a condition about an answer from being put to a composer at all.
     *
     * <p>The reading's own answers. Each says what this reading has no way of saying rather than
     * what the model says, and each names something an author could write another way.
     */
    sealed interface WhyNotStated {

        /**
         * A truth read off a place inside the answer.
         *
         * <p>A {@code Bool} divides a position into two values and puts nothing under it, so a
         * truth of the answer itself is the value and is stated. A truth of a field is a demand
         * about a place this reading has no way of putting a value at, and composing for the
         * field's type instead would meet the type and not the demand.
         */
        record ATruthOfAPlaceInsideTheAnswer() implements WhyNotStated {}

        /**
         * A comparison over more than this one answer.
         *
         * <p>A form over two answers, or over an answer and a number of the input, is one statement
         * about the pair: which value either may take depends on what the other took, and nothing
         * here composes two values to it together. Split into a demand apiece, each half would be
         * met by a value the pair does not satisfy.
         */
        record AFormOverMoreThanOneAnswer() implements WhyNotStated {}

        /**
         * A place on the answer's own order rather than a form over its numbers.
         *
         * <p>What a carrier that counts nothing states is where on its order a value lies, which is
         * a value and not a quantity. What this stage composes an answer against is a form, so such
         * a column has nowhere to go.
         */
        record APlaceOnTheAnswersOwnOrder() implements WhyNotStated {}
    }

    /**
     * What stopped a stated demand from being composed against.
     *
     * <p>The composer's own answers, and they are about the answer's positions rather than the
     * input's. A value is composed without the demand either way, so nothing read off one of these
     * says no value meets it.
     */
    sealed interface WhyNotComposed {

        /**
         * The region over the answer measures the term on no order.
         *
         * <p>Which is the region's answer and not a reading of the form's shape. A difference
         * between two positions holding records is read from end to end and is a distance on
         * nothing, and what an author has to act on is that the model's own type carries no order.
         *
         * <p>The term is what the refusal named and is what tells two refusals of one demand apart.
         * It is not said to an author: it is spelled in the subject the answer was composed over,
         * whose head is a name of the composer's own.
         */
        record NoOrderUnderATermOfTheAnswer(NumericTerm term) implements WhyNotComposed {

            public NoOrderUnderATermOfTheAnswer {
                if (term == null) {
                    throw new IllegalArgumentException(
                            "a term standing on no order is some term of the answer");
                }
            }
        }

        /**
         * The demand was taken into the region and no value was composed at the positions it is
         * over.
         *
         * <p>Said of the whole demand, for the reason the same word on the input side is: a form
         * over two places is one statement about the pair, and a value put at one of them on the
         * strength of it is a value the demand does not hold of.
         */
        record NoValueComposedAtItsPositions() implements WhyNotComposed {}
    }
}
