package souther.compiler.execute;

import java.util.Objects;
import java.util.Optional;

/**
 * Where a run stopped without answering, in the terms the generated code and the runtime said it
 * in: a construction its type's invariant refused, an {@code ensures} that did not hold, an
 * operation the language refuses to finish, or an {@code unreachable} reached.
 *
 * <p>Beside what the run answered and never part of it. A run that stopped answered nothing,
 * whatever stopped it, and two runs that answered nothing answered alike; where one stopped is a
 * separate fact, read by a reader that has to tell an author which input the model has not decided
 * about. A run that went past what a run may spend did not stop of its own accord and is none of
 * these.
 */
public sealed interface RunStop {

    /** Which of the language's ends a run stopped at, as one word apiece. */
    enum Kind {
        A_CONSTRUCTION,
        AN_ENSURES,
        AN_END,
        AN_UNREACHABLE
    }

    /** Which of them this is. */
    default Kind kind() {
        return switch (this) {
            case AtAConstruction _ -> Kind.A_CONSTRUCTION;
            case AtAnEnsures _ -> Kind.AN_ENSURES;
            case AtAnEnd _ -> Kind.AN_END;
            case AtAnUnreachable _ -> Kind.AN_UNREACHABLE;
        };
    }

    /** The module whose source the place the run stopped at is written in, where it has one. */
    Optional<String> writtenIn();

    /**
     * A construction one of its type's invariant clauses refused.
     *
     * <p>Which clause by the declaration that wrote it and its place among that declaration's
     * clauses, which a clause has whether or not it was named. Where the construction is by the
     * module whose code wrote it and the line and column it starts at; a construction the generated
     * code had no place for has none ({@code line} of nought).
     *
     * @param clauseModule the module of the declaration that wrote the clause
     * @param clauseType   that declaration
     * @param clauseName   the clause's name, where it was declared with one
     * @param ordinal      the clause's place among that declaration's clauses, from nought
     * @param siteModule   the module whose code wrote the construction
     * @param line         the line it starts at, from one; nought where it has no place
     * @param column       the column it starts at, from one
     */
    record AtAConstruction(String clauseModule, String clauseType, Optional<String> clauseName,
                           int ordinal, String siteModule, int line, int column)
            implements RunStop {

        public AtAConstruction {
            Objects.requireNonNull(clauseModule, "a clause is written in some module");
            Objects.requireNonNull(clauseType, "a clause is written on some declaration");
            Objects.requireNonNull(clauseName, "a clause was declared with a name or without one");
            Objects.requireNonNull(siteModule, "a construction is written in some module");
        }

        /** Whether the code that refused it said where the construction is. */
        public boolean placed() {
            return line > 0;
        }

        @Override
        public Optional<String> writtenIn() {
            return Optional.of(siteModule);
        }
    }

    /**
     * An {@code ensures} of a behavior the answer did not keep.
     *
     * @param module   the behavior's module
     * @param behavior the behavior
     * @param clause   the clause's name, where the rule was written as named clauses
     */
    record AtAnEnsures(String module, String behavior, Optional<String> clause)
            implements RunStop {

        public AtAnEnsures {
            Objects.requireNonNull(module, "a behavior is declared in some module");
            Objects.requireNonNull(behavior, "an ensures is a behavior's");
            Objects.requireNonNull(clause, "an ensures was written with a name or without one");
        }

        @Override
        public Optional<String> writtenIn() {
            return Optional.of(module);
        }
    }

    /**
     * An operation the language refuses to finish — a number past what its type holds, a division
     * by zero — in the runtime's own words for it. The runtime says no place, so this has none.
     *
     * @param said what the runtime said ended the run
     */
    record AtAnEnd(String said) implements RunStop {

        public AtAnEnd {
            Objects.requireNonNull(said, "an end is said as something");
        }

        @Override
        public Optional<String> writtenIn() {
            return Optional.empty();
        }
    }

    /**
     * An {@code unreachable} the run reached, with what the code said there.
     *
     * @param said what the reached {@code unreachable} said
     */
    record AtAnUnreachable(String said) implements RunStop {

        public AtAnUnreachable {
            Objects.requireNonNull(said, "an unreachable says something when it is reached");
        }

        @Override
        public Optional<String> writtenIn() {
            return Optional.empty();
        }
    }
}
