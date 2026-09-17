package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

import java.util.List;

/**
 * What each of one quantity's terms came to at one row, before anything is made of the numbers.
 *
 * <p>The row read, and not an answer about it. {@link BorderQuantity#standsAt} ranks what the terms
 * came to one way and {@link BorderQuantity#valuesOf} ranks it another — a position the row wrote
 * nothing at outranks what stopped a reading for the first and is put together with it for the
 * second — so neither of their answers can be had from the other, and a walk of the row that came
 * back as either would be a walk the other question has to make again.
 *
 * <p><b>A sequence and not a map from term to reading.</b> Which end of a distance is which decides
 * the sign of it, and what a map holds is the same whichever order its entries were put in. Read
 * back from a reading, the ends would be told apart by whatever order a walk happened to record
 * them in, and two readings that stand opposite ways round would be equal.
 *
 * <p>No criterion here. A row and a quantity make a reading; a criterion is what a reading is then
 * asked about. Read with one in hand, a second criterion would be a second walk of the row.
 *
 * <p>What a term came to is this package's to read. A caller outside it holds a reading, hands it
 * back to the quantity that made it and is answered; what the arms of a term's reading are and which
 * of them outranks which is the quantity's business, and a reader that took them apart for itself
 * would be the second place that has to rank them.
 */
public record QuantityReading(List<OfATerm> terms) {

    public QuantityReading {
        if (terms == null || terms.isEmpty()) {
            throw new IllegalArgumentException(
                    "a quantity is taken of at least one term, so a reading of one reads at least"
                            + " one term");
        }
        terms = List.copyOf(terms);
    }

    /**
     * What the quantity read at {@code term}.
     *
     * <p>Asked by the term and not by where it fell, so that a quantity reading two of them cannot
     * take one end for the other. A reading of some other quantity is refused rather than answered
     * for: it is not a term this went without, it is a reading of a row this is not a reading of.
     */
    WhatATermRead of(NumericTerm term) {
        for (OfATerm each : terms) {
            if (each.term().equals(term)) {
                return each.read();
            }
        }
        throw new IllegalArgumentException("this reads " + terms.stream().map(OfATerm::term).toList()
                + " and was asked what it read at " + term);
    }

    /** What one term came to, beside the term it is of. */
    public record OfATerm(NumericTerm term, WhatATermRead read) {

        public OfATerm {
            if (term == null || read == null) {
                throw new IllegalArgumentException(
                        "a term's reading is a term and what it came to: " + term + " " + read);
            }
        }
    }
}
