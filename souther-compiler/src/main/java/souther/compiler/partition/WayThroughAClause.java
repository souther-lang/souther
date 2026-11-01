package souther.compiler.partition;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputReading;

import java.util.List;

/**
 * The way to the next statement of one rule of an {@code ensures}: what the statements before it
 * have to have come out as for a run to evaluate it at all.
 *
 * <p>A clause is evaluated as it is written. The conjuncts of one rule run left to right and a run
 * is aborted at the first that does not hold, so a statement is evaluated only where every one
 * before it held. That is the whole of what is used here, and it is used only for what a
 * statement owes about being read — whether a run can evaluate it — and never for the lines the
 * clause draws, which are what the relation changes at and do not turn on the order it is written
 * in ({@link EnsuresThresholds}).
 *
 * <p><b>Of one rule and no further.</b> Another rule of the same declaration is run whether or not
 * this one applied, and it applies for a case of its own; what one rule held says nothing of
 * whether the next is evaluated.
 *
 * <p><b>Only what is said as a condition.</b> A statement this reading takes in as a comparison is
 * put on the way as the condition it is. A form nothing here reads, a predicate over strings, and a
 * choice are put on nothing: leaving a condition off a way only widens it, and a way that cannot be
 * shown empty keeps what is owed. A conjunct that did not type is left off for the same reason.
 *
 * <p>Held as being true and not as having been evaluated to the end: a statement that stopped the
 * run is one no later statement is evaluated after, which only makes later statements less
 * reached, and a way is dropped from owing only on a proof it holds no row.
 */
final class WayThroughAClause {

    private final InputReading read;
    private final Symbols symbols;
    private final DeclarationNewtypes newtypes;
    private final WhatConditionsState conditions;
    private final ConditionNumbering numbering;
    private List<OnTheWay> way = List.of();

    WayThroughAClause(String behavior, InputReading read) {
        this.read = read;
        this.symbols = read.symbols();
        this.newtypes = read.newtypes();
        this.conditions = WhatConditionsState.of(read);
        this.numbering = new ConditionNumbering(symbols.module(), behavior,
                ConditionOccurrence.Reading.DIVIDING);
    }

    /**
     * Whether the next statement may be evaluated: the way to it is not shown to hold no row of
     * what the declarations leave.
     */
    boolean mayReachTheNext() {
        return Reachability.of(new WayToTheBorder(way), read.quantities().region()).leavesARow();
    }

    /** That the statement {@code said} has been evaluated, and held. */
    void held(ClauseStatements.Statement said) {
        if (said instanceof ClauseStatements.Statement.Compares comparison) {
            way = ComparisonReadings.taking(Condition.of(comparison.stated(), comparison.reads(),
                    symbols, newtypes, numbering), true, read, way, conditions, numbering);
        }
    }
}
