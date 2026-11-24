package souther.compiler.execute;

import java.util.Comparator;
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
     * These in a steady order, which two of them are equal in only where they are equal: the kind,
     * then whatever the kind holds, in the order its components are declared.
     *
     * <p>Steady and nothing else. What comes first says nothing about a model; it is what keeps
     * one compiler over one source writing the places runs stopped at in one order.
     */
    Comparator<RunStop> IN_A_STEADY_ORDER = Comparator.comparing(RunStop::kind)
            .thenComparing(RunStop::byWhatItHolds);

    /** Two of one kind, by what that kind holds. Asked only where the kinds agree. */
    private static int byWhatItHolds(RunStop one, RunStop other) {
        Comparator<Optional<String>> named = Comparator.comparing(
                each -> each.orElse(null), Comparator.nullsFirst(Comparator.naturalOrder()));
        Comparator<Optional<Site>> placed = Comparator.comparing(
                each -> each.orElse(null), Comparator.nullsFirst(Site.IN_A_STEADY_ORDER));
        return switch (one) {
            case AtAConstruction it -> Comparator.comparing(AtAConstruction::clauseModule)
                    .thenComparing(AtAConstruction::clauseType)
                    .thenComparing(AtAConstruction::clauseName, named)
                    .thenComparingInt(AtAConstruction::ordinal)
                    .thenComparing(AtAConstruction::site, placed)
                    .compare(it, (AtAConstruction) other);
            case AtAnEnsures it -> Comparator.comparing(AtAnEnsures::module)
                    .thenComparing(AtAnEnsures::behavior)
                    .thenComparing(AtAnEnsures::clause, named)
                    .compare(it, (AtAnEnsures) other);
            case AtAnEnd it -> it.said().compareTo(((AtAnEnd) other).said());
            case AtAnUnreachable it -> Comparator.comparing(AtAnUnreachable::said)
                    .thenComparing(AtAnUnreachable::site, placed)
                    .compare(it, (AtAnUnreachable) other);
        };
    }

    /**
     * Where a construction or an {@code unreachable} is written, as the code that stopped the run
     * said it: the module whose text it is in, which for one inlined from another module's helper
     * is that module, and the line and column it starts at there.
     *
     * <p>All three or none. The code generator says a place only where this compilation held the
     * text laid out, and a stop it said none for has no place here rather than another module's
     * name in its stead.
     *
     * @param module the module whose text it is written in
     * @param line   the line it starts at, from one
     * @param column the column it starts at, from one
     */
    record Site(String module, int line, int column) {

        /** These in a steady order: the module, then the line, then the column. */
        static final Comparator<Site> IN_A_STEADY_ORDER = Comparator.comparing(Site::module)
                .thenComparingInt(Site::line).thenComparingInt(Site::column);

        public Site {
            Objects.requireNonNull(module, "a place is written in some module's text");
            if (line < 1) {
                throw new IllegalArgumentException("a place is at a line, from one: " + line);
            }
        }
    }

    /**
     * A construction one of its type's invariant clauses refused.
     *
     * <p>Which clause by the declaration that wrote it and its place among that declaration's
     * clauses, which a clause has whether or not it was named. Where the construction is written,
     * where the code that refused it said ({@link Site}).
     *
     * @param clauseModule the module of the declaration that wrote the clause
     * @param clauseType   that declaration
     * @param clauseName   the clause's name, where it was declared with one
     * @param ordinal      the clause's place among that declaration's clauses, from nought
     * @param site         where the construction is written, or none where the code that refused
     *                     it said no place
     */
    record AtAConstruction(String clauseModule, String clauseType, Optional<String> clauseName,
                           int ordinal, Optional<Site> site)
            implements RunStop {

        public AtAConstruction {
            Objects.requireNonNull(clauseModule, "a clause is written in some module");
            Objects.requireNonNull(clauseType, "a clause is written on some declaration");
            Objects.requireNonNull(clauseName, "a clause was declared with a name or without one");
            Objects.requireNonNull(site, "a construction was said to be somewhere or nowhere");
        }

        @Override
        public Optional<String> writtenIn() {
            return site.map(Site::module);
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
     * An {@code unreachable} the run reached, with what the code said there and where it is
     * written, where the code that reached it said ({@link Site}).
     *
     * @param said what the reached {@code unreachable} said
     * @param site where it is written, or none where the code that reached it said no place
     */
    record AtAnUnreachable(String said, Optional<Site> site) implements RunStop {

        public AtAnUnreachable {
            Objects.requireNonNull(said, "an unreachable says something when it is reached");
            Objects.requireNonNull(site, "an unreachable was said to be somewhere or nowhere");
        }

        @Override
        public Optional<String> writtenIn() {
            return site.map(Site::module);
        }
    }
}
