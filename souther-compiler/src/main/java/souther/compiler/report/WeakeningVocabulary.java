package souther.compiler.report;

import souther.compiler.observe.Incompleteness;
import souther.compiler.publish.PublicationOrders;

/**
 * The word a document writes for one weakening, out of either vocabulary it can come from.
 *
 * <p>Two vocabularies and one array. A weakening that is an observation gone missing writes the
 * observation code's own word, because that vocabulary already exists and a second spelling of it
 * would be a second thing to keep in step ({@link WeakeningWord}); everything else writes a word of
 * this document's. So what the array holds is one of the two.
 *
 * <p>Which is what this is for. The array is a set of words and a document writes a sequence, so
 * the words take an order, and an order is over one kind. Named, the two vocabularies are one kind
 * with one order over it
 * ({@link PublicationOrders#WEAKENING_WORDS}). Unnamed, there is no kind
 * to put in order and the sequence falls to whatever the words were collected in.
 *
 * <p>No word of its own. What each of these is called is the word of what it holds, said where
 * every other word of this document is said.
 */
public sealed interface WeakeningVocabulary {

    /** A weakening that is an observation gone missing, which writes the observation's own code. */
    record AnObservationCode(Incompleteness.Code code) implements WeakeningVocabulary {}

    /** Every other weakening, which writes a word this document has for it. */
    record AWordOfThisDocuments(WeakeningWord word) implements WeakeningVocabulary {}
}
