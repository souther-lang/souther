package souther.compiler.query;

import souther.compiler.observe.ArmObservation;

/**
 * What a compilation was asked to observe of its rows.
 *
 * <p>One capability and not several questions, because the rows run once and what they were built
 * to record is settled before they do. Every consumer of one compilation gets that one run, so what
 * is held is what they need between them.
 *
 * <p>Ordered, unlike {@link HowALineIsRead}. Each of these is everything the one before it is and
 * more — recording where a row went is of no use to anybody who is not reading the rows — so two
 * callers asking for different ones are answered by the wider, and a caller asking for less does
 * not take anything away from one that asked for more.
 *
 * <p>What a build asked to be told about is not this. A level is one consumer stating what its
 * report needs ({@link Compilation#measure}); an editor about to compose rows is another, and it
 * needs the same things without wanting the report.
 */
public enum RowObservation {

    /** Nothing is read of the rows. They still run — every row of an evaluated source does — and
     *  nothing is asked of what they came to. */
    NONE,

    /** What the rows came to is read. Which of a body's arms each of them went through is not:
     *  that takes a second set of classes and every row run again. */
    READ,

    /** That, and the classes record where each row went. */
    RECORD_ARMS;

    /** Whether anything is asked of what the rows came to. */
    public boolean readsRows() {
        return this != NONE;
    }

    /** What the classes these rows run against are built to record. */
    public ArmObservation arms() {
        return this == RECORD_ARMS ? ArmObservation.RECORD : ArmObservation.OMIT;
    }

    /** The wider of two, which is what one compilation answers two callers with. */
    public RowObservation and(RowObservation other) {
        return compareTo(other) >= 0 ? this : other;
    }
}
