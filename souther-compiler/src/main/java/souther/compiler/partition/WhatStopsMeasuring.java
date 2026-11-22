package souther.compiler.partition;

import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.Figure;

import java.util.Optional;

/**
 * The figure measuring one body runs into, told as its constructs are read and before any line of
 * it is asked where it decides or searched.
 *
 * <p>Two things multiply on the way to what is measured, and each is held to a figure of its own
 * that gives up what is past it. The readings of one condition multiply with each choice its values
 * are made through ({@link CompositionBudget#TOTAL_READINGS_OF_ONE_CONDITION}): a condition is past
 * it where its reading stopped there. The cases the lines of one statement are asked in multiply
 * with each choice on the way to them ({@link CompositionBudget#QUESTIONS_A_STATEMENT_IS_ASKED}):
 * the cases are held as the choices they are made of ({@link DecidingCase.Cases}), so how many ways
 * there are of choosing one is counted without choosing, and a statement whose lines have more of
 * them than it is asked questions is past it.
 *
 * <p>So a body told of here is dear to measure as it is written, and not measured whole for it:
 * the work up to the figure is done and what is past it is said not to be. Told once, at the first
 * that is met, so that reading the rest of the body is not paid for.
 */
final class WhatStopsMeasuring {

    private Figure stops;

    /** Takes in what a condition was read to state. */
    void reading(Proposition stated) {
        Figure inAll = CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.reached();
        if (Proposition.figuresOfReadingsIn(stated).contains(inAll)) {
            stops = inAll;
        }
    }

    /** Takes in the lines of one statement, read as {@code standing}. */
    void drawing(BoundaryPolicy.Standing standing) {
        if (standing instanceof BoundaryPolicy.Standing.Admitted(var read) && casesAtMost(read)
                > CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED.maximum()) {
            stops = CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED.reached();
        }
    }

    /** Whether measuring the body was shown to run into a figure. */
    boolean isShown() {
        return stops != null;
    }

    /** The figure measuring the body runs into; empty where it was shown to run into none. */
    Optional<Figure> figure() {
        return Optional.ofNullable(stops);
    }

    /** How many cases the lines of one statement are asked in at most: one line of its own is
     *  asked where it stands, and a line of several in no more of its cases than it is taken apart
     *  into. */
    private static long casesAtMost(ComparisonAssessment read) {
        if (!(read instanceof ComparisonAssessment.Several several)) {
            return 1;
        }
        long out = 0;
        for (ComparisonAssessment.Several.Part part : several.parts()) {
            if (part.line() instanceof ComparisonAssessment.Several lines) {
                out += casesAtMost(lines);
            } else {
                for (DecidingCase each : part.cases()) {
                    long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
                    out += Math.min(most, each.standsFor().waysOfChoosing(most));
                }
            }
        }
        return out;
    }
}
