package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What each conjunct of a declaration's invariants states, statement by statement.
 *
 * <p>The one way from a conjunct an author wrote to what it says. A conjunct states as many
 * statements as a reading of its shape arrives at — a denial carried into a choice states one per
 * branch, and a helper whose body joins two rules states both — and each of them is recognised
 * where the clause's connectives were read once ({@link ClauseExpr}) rather than off the tree the
 * expansion left.
 *
 * <p><b>What crosses here is what a statement states.</b> A comparison arrives with its denial and
 * its orientation already spent, and an operation arrives as the operation it is. A consumer handed
 * the conjunct's tree instead reads the shape a second time, which is the reading that has no word
 * for a binding and no word for a denial — and an author who named a rule loses what an author who
 * repeated it keeps.
 *
 * <p><b>Every statement or none.</b> A conjunct answers with all of what it states, the ones this
 * made nothing of included ({@link InvariantStatement.Unread}), so a consumer acting on part of a
 * conjunct can see that it is a part. Answering with the recognised ones alone, a conjunct stating
 * two rules would be indistinguishable from one stating the rule that was recognised.
 */
public final class InvariantStatements {

    private final Terms terms;
    private final Clauses clauses;
    /** One answer per declaration, because a conjunct is asked about once per consumer and the
     *  clauses of a declaration are read to answer for any of them. */
    private final Map<TypeSymbol.AtModule, Map<PartId<RuleRef.Invariant>, List<InvariantStatement>>>
            read = new LinkedHashMap<>();

    private InvariantStatements(Terms terms, Clauses clauses) {
        this.terms = terms;
        this.clauses = clauses;
    }

    /**
     * The calls a conjunct states, for a consumer that reads nothing else of it. A comparison is
     * {@link InvariantStatement.Unread} here: what a comparison states takes a reading of the
     * declarations ({@link #of(RuleReadingContext)}), and a consumer of calls has no budget to
     * read under.
     */
    public static InvariantStatements ofTheCalls(RuleReadingSource source) {
        return new InvariantStatements(null, new Clauses(source));
    }

    /**
     * The statements of the declarations {@code reading} reads.
     *
     * <p>Over a reading and not a source alone: a comparison of the sign of an order states the
     * order of its arguments only where the values can be named, which is {@link Terms}' to say.
     */
    public static InvariantStatements of(RuleReadingContext reading) {
        Terms terms = new Terms(Terms.Of.THE_DISCHARGE_TREE, reading);
        return new InvariantStatements(terms, terms.clauses());
    }

    /**
     * What {@code part} states, or null where the reading has no form for the clause it is of.
     *
     * <p>Null and not an empty list. A conjunct states at least one thing — the walk that numbers
     * the statements arrives at a part however little is made of it — so an empty answer could only
     * mean a clause that was never read, and a consumer reading it as "this conjunct constrains
     * nothing" would drop the rule.
     */
    public List<InvariantStatement> of(PartId<RuleRef.Invariant> part) {
        return statesOf(part.rule().clause().id().declaredOn()).get(part);
    }

    private Map<PartId<RuleRef.Invariant>, List<InvariantStatement>> statesOf(
            TypeSymbol.AtModule declaration) {
        return read.computeIfAbsent(declaration, named -> {
            Map<PartId<RuleRef.Invariant>, List<InvariantStatement>> out = new LinkedHashMap<>();
            Denotations at = terms == null ? Denotations.none() : Denotations.none().locations(
                    clauses.bindingsOf(named).values(), terms::placeSubject, terms::placeTerm);
            for (ClauseMeaning clause : clauses.declared(named)) {
                Clauses.AsStated stated = clauses.stated(clause);
                if (stated == null) {
                    continue;
                }
                // The parts as subtrees of the one reading of the clause, read where every other
                // reader of a declaration's rules reads them. Read into a shape here, this would be
                // a second answer to what the clause's author wrote.
                for (Clauses.StatedPart part : clauses.partsOf(stated)) {
                    out.put(part.id(), statementsOf(part, at));
                }
            }
            return Map.copyOf(out);
        });
    }

    private List<InvariantStatement> statementsOf(Clauses.StatedPart part, Denotations at) {
        List<InvariantStatement> out = new ArrayList<>();
        for (ConjunctStatements.Reached each : ConjunctStatements.of(part.of(), part.id())) {
            out.add(states(each, at));
        }
        return List.copyOf(out);
    }

    private InvariantStatement states(ConjunctStatements.Reached reached, Denotations at) {
        // What the names under the bindings mean, which is what entering them comes to here. A
        // consumer handed the bindings instead reads a rule about the helper's parameter and has to
        // work out which of the declaration's values that parameter stands for — which is the
        // reading that has no word for a helper, arriving one reader further on.
        Map<BindingId, Core> given = new LinkedHashMap<>();
        Denotations inside = at;
        for (ClauseExpr.Scoped each : reached.crossed()) {
            Core.LetIn binding = each.binding();
            given.put(binding.binder().binding(), Clauses.substituted(binding.value(), given));
            if (terms != null) {
                inside = terms.inside(binding, inside);
            }
        }
        // Of the part and its polarity together, so what comes back is the comparison the clause
        // states rather than the one its author spelled — the order of the arguments where it
        // compares the sign of an order. Read as it was written, in the environment the bindings
        // make, as every other reader of a clause reads a name: a value named twice is then read
        // once per name and not once per path through the tree its names spell. What comes back is
        // spent afterwards, since it is handed on to readers with no environment of their own.
        if (terms != null
                && Core.withoutStanding(reached.said().of()) instanceof Core.Binary written) {
            StatedComparison compares =
                    Conditions.statedBy(terms, written, reached.said().positive(), inside);
            if (compares != null) {
                return new InvariantStatement.Compares(reached.statement(),
                        new StatedComparison(compares.claim(),
                                Clauses.substituted(compares.left(), given),
                                Clauses.substituted(compares.right(), given), compares.reading()));
            }
        }
        // What the part states with the denials above it taken off, which is the operation itself
        // where one was kept standing. Stated only: what holds where an operation does not is not
        // that operation, and there is nothing here to name it by.
        if (reached.said().positive()
                && Core.withoutStanding(Clauses.substituted(reached.said().of(), given))
                        instanceof Core.PreservedCall call) {
            return new InvariantStatement.Applies(reached.statement(), call);
        }
        // A lookup in a map followed to a statement about what it found: stated as the entry the
        // rule asks the map for, which no operation the representation kept standing says.
        EntryHeld.Stated entry = reached.said().positive()
                ? EntryHeld.read(Clauses.substituted(reached.said().of(), given), core -> core)
                : null;
        if (entry != null) {
            return new InvariantStatement.HoldsAnEntry(reached.statement(), entry);
        }
        return new InvariantStatement.Unread(reached.statement());
    }
}
