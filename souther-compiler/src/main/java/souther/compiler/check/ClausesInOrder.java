package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * Every clause that governs a value being built, in the order a construction checks them, each read
 * where its fields are given what the construction hands them — or unread, with why.
 *
 * <p>In order, and the unread ones in their places. Which clause a failure names is the first that
 * does not hold, so what an arm answering a clause means is that every clause before it held: a
 * clause this reading has no form for, standing before it, is part of that, and a list of the ones
 * read with the rest set aside would leave an arm meaning less than it does.
 *
 * <p>The order is the one the value is checked in where it runs: the clauses of what the
 * declaration spreads, each spread in turn, and then its own, each declaration's in the order it
 * writes them.
 *
 * @param inOrder          the clauses, in the order a construction checks them
 * @param everyRuleReached whether every declaration whose clauses govern the value was reached, so
 *                         that no clause is missing from {@code inOrder}
 */
public record ClausesInOrder(List<OneClause> inOrder, boolean everyRuleReached) {

    public ClausesInOrder {
        inOrder = List.copyOf(inOrder);
    }

    /** One clause, as it reads at the construction. */
    public sealed interface OneClause {

        /** Which clause of which declaration this is, and what a sentence calls it. */
        Clause.Ref clause();

        /**
         * The clause, and what the construction hands each field it reads.
         *
         * <p>The two are kept apart because they are written in different trees. The term is the
         * one the declaration's own analysis reads, which keeps the language's operations standing
         * as calls; the values are expressions of the body that builds the value, in whichever
         * tree that body is read. A reader that reads the two in one tree asks for
         * {@link #substituted}; one that reads them in their own trees hands each value to the
         * field it is for.
         *
         * @param term  what the clause states, over the declaration's fields
         * @param given what the construction hands each field, in the order it writes them
         * @param parts the rules its author wrote it as
         */
        record Stated(Clause.Ref clause, Core term, Map<BindingId, Core> given,
                      ClauseMeaning.Parts parts) implements OneClause {

            public Stated {
                Objects.requireNonNull(clause, "a clause read is some clause");
                Objects.requireNonNull(term, "a clause read states something");
                Objects.requireNonNull(parts, "a clause is written as some rules");
                given = Collections.unmodifiableMap(new LinkedHashMap<>(given));
            }

            /** The term with each field replaced by the value it is handed, as one expression. */
            public Core substituted() {
                return Clauses.substituted(term, given);
            }
        }

        /** The clause, which this reading could not read at the construction, and why. */
        record Unread(Clause.Ref clause, WhyAClauseIsUnread why) implements OneClause {

            public Unread {
                Objects.requireNonNull(clause, "a clause left unread is some clause");
                Objects.requireNonNull(why, "a clause is left unread for some reason");
            }
        }
    }

    /** Why a clause was not read at a construction. */
    public enum WhyAClauseIsUnread {

        /** The declaration publishes no form for the clause, so its run-time check is the whole of
         *  what is known of it. */
        NO_FORM,

        /** The clause reads a field the construction gives no value, so it names a value that is
         *  not there. */
        A_FIELD_LEFT_OUT
    }

    /**
     * The clauses that govern what {@code construct} builds, each read where its fields are given
     * the values {@code construct} hands them, as {@code source} publishes the declarations.
     */
    public static ClausesInOrder at(Core.Construct construct, RuleReadingSource source) {
        Clauses clauses = new Clauses(source);
        Map<String, BindingId> fields = clauses.bindingsOf(construct.typeName());
        Map<BindingId, Core> given = new LinkedHashMap<>();
        for (Core.FieldValue value : construct.values()) {
            BindingId field = fields.get(value.field());
            if (field != null) {
                given.put(field, value.value());
            }
        }
        return clauses.inOrder(construct.typeName(), given);
    }
}
