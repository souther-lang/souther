package souther.compiler.execute;

import java.util.Objects;
import java.util.Optional;

/**
 * A construction a run stopped at because one of its type's invariant clauses did not hold, in the
 * terms the generated code said it in.
 *
 * <p>Beside what the run answered and never part of it. A run that stopped answered nothing,
 * whatever stopped it, and two runs that answered nothing answered alike; what stopped one is a
 * separate fact, read by a reader that has to tell an author which input the model has not decided
 * about.
 *
 * <p>Which clause by the declaration that wrote it and its place among that declaration's clauses,
 * which a clause has whether or not it was named. Where the construction is by the module whose code
 * wrote it and the line and column it starts at; a construction the generated code had no place for
 * has none ({@code line} of nought).
 *
 * @param clauseModule the module of the declaration that wrote the clause
 * @param clauseType   that declaration
 * @param clauseName   the clause's name, where it was declared with one
 * @param ordinal      the clause's place among that declaration's clauses, from nought
 * @param siteModule   the module whose code wrote the construction
 * @param line         the line it starts at, from one; nought where it has no place
 * @param column       the column it starts at, from one
 */
public record RefusedConstruction(String clauseModule, String clauseType,
                                  Optional<String> clauseName, int ordinal, String siteModule,
                                  int line, int column) {

    public RefusedConstruction {
        Objects.requireNonNull(clauseModule, "a clause is written in some module");
        Objects.requireNonNull(clauseType, "a clause is written on some declaration");
        Objects.requireNonNull(clauseName, "a clause was declared with a name or without one");
        Objects.requireNonNull(siteModule, "a construction is written in some module");
    }

    /** Whether the code that refused it said where the construction is. */
    public boolean placed() {
        return line > 0;
    }
}
