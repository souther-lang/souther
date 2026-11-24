package souther.compiler.check;

import souther.compiler.check.InvariantChecker.ClauseJudgments;
import souther.compiler.check.InvariantChecker.Judged;
import souther.compiler.check.InvariantChecker.Judgment;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.core.Core;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * What each clause of a construction's invariant comes to where the construction stands.
 *
 * <p>One question with two readers. The discharge check reports off it, and the reading of what
 * arrives at an attempt's arms enters them by it: an attempt's departure is taken where a clause
 * it answers fails, so a departure whose clauses are established where the attempt stands is one
 * nothing enters. Each reader asks it over the tree it walks. The check's reading is kept beside
 * the tree it read ({@link DeparturesNoRunTakes}), so where the tree that runs says less — an
 * operation it holds as the walk it lowers to — what the check found still shuts the departure.
 *
 * <p>Held by the {@link PathEngine} whose rules it reads by, so that the terms, the predicates and
 * the declarations' clauses are the ones the walk asking it was entering by.
 */
final class ConstructionVerdicts {

    /** Which form each declaration was written in. What a construction is judged against turns on
     *  the form its name was declared in, which was settled when the module was indexed. */
    private final DeclarationKinds kinds;
    private final DeclarationNewtypes newtypes;
    private final Clauses clauses;
    private final Terms terms;
    private final Predicates predicates;

    ConstructionVerdicts(DeclarationKinds kinds, DeclarationNewtypes newtypes, Clauses clauses,
                         Terms terms, Predicates predicates) {
        this.kinds = kinds;
        this.newtypes = newtypes;
        this.clauses = clauses;
        this.terms = terms;
        this.predicates = predicates;
    }

    /**
     * The product {@code made} builds, or null where it builds anything else: only a product
     * carries an invariant to judge a construction against.
     */
    TypeSymbol.AtModule productOf(Core.Construct made) {
        // Which form the name was declared in, asked of what was settled when its module was
        // indexed. Reading the declaration to find that out is what had this check re-run for a
        // declaration of another module that had only moved.
        return made.typeName() instanceof TypeSymbol.AtModule type
                && kinds.of(type.key()) == DeclarationKind.PRODUCT ? type : null;
    }

    /**
     * The verdict for one construction of the product {@code type} ({@link #productOf}), over what
     * each field is being given, or null where the conditions on the path leave no way to it. A
     * case split never reaches here: the walk opens it before anything is checked, so what a field
     * is given is a value and not a choice of arms.
     */
    Judgment of(Core.Construct nd, TypeSymbol.AtModule type, Known k, Denotations at,
                ContextMultiplicity copies) {
        return verdictOf(type, given(nd, at), k, at, !constantlyBuilt(type, nd), copies);
    }

    /**
     * Each departure of {@code attempt}, in the order it is written, as whether no run takes it
     * where the attempt stands under {@code k}.
     *
     * <p>Read off what the attempt's clauses come to there ({@link #of}). A departure is taken
     * where the first clause not to hold is one it answers
     * ({@link Choice.Decides.ItDeparted#answers}), so none is taken where each clause it answers
     * holds. A clause this could not read holds nowhere it says, and a departure answering it may be
     * taken; so may every departure of an attempt some declaration of whose clauses was not reached.
     *
     * <p>Nothing about the value built. A clause the value fails wherever it is attempted is
     * refused before anything is run, so the arms are asked about only where none is.
     *
     * <p>Where no way the conditions on the path come apart in reaches the attempt, no departure is
     * taken. Where the attempt builds something that carries no invariant, nothing is said.
     */
    List<Boolean> departuresNoRunTakes(Core.IfConstructed attempt, Known k, Denotations at,
                                       ContextMultiplicity copies) {
        int departures = attempt.els().size();
        TypeSymbol.AtModule type = productOf(attempt.construct());
        if (type == null) {
            return Collections.nCopies(departures, false);
        }
        return departuresUnder(attempt, type, of(attempt.construct(), type, k, at, copies), at);
    }

    /**
     * The same, where the attempt's construction, of the product {@code type}, came to
     * {@code judged} where it stands ({@link #of}) — null where no way the conditions on the path
     * come apart in reaches it.
     */
    List<Boolean> departuresUnder(Core.IfConstructed attempt, TypeSymbol.AtModule type,
                                  Judgment judged, Denotations at) {
        if (judged == null) {
            return Collections.nCopies(attempt.els().size(), true);
        }
        ClausesInOrder inOrder = clauses.inOrder(type, given(attempt.construct(), at));
        List<Boolean> out = new ArrayList<>();
        for (Core.ElseArm arm : attempt.els()) {
            Choice.Decides.ItDeparted departure = Choice.Decides.ofDeparture(attempt, arm);
            out.add(inOrder.everyRuleReached() && inOrder.inOrder().stream()
                    .map(ClausesInOrder.OneClause::clause)
                    .filter(departure::answers)
                    .allMatch(clause -> judged.held().contains(clause.id())));
        }
        return List.copyOf(out);
    }

    /** What {@code nd} hands each field a clause reads, by the field's binding. */
    private Map<BindingId, Core> given(Core.Construct nd, Denotations at) {
        Map<String, BindingId> fields = clauses.bindingsOf(nd.typeName());
        Map<BindingId, Core> given = new HashMap<>();
        for (Core.FieldValue fv : nd.values()) {
            BindingId field = fields.get(fv.field());
            if (field == null) {
                continue;
            }
            // A name given a value written out hands over that value: the clause folds over what
            // was written, wherever the writing was done.
            Core written = terms.writtenValue(fv.value(), at);
            given.put(field, written != null ? written : fv.value());
        }
        return given;
    }

    /**
     * The verdict for a construction of {@code named}, with the conditions on the path that hold as
     * one of their parts taken apart where the whole of each leaves the invariant not shown to
     * hold — or null where no combination of their parts is entered, so no value is built here.
     *
     * <p>Only there. A clause established without them is established in each way they could be
     * taken apart, since each way knows more than this; so is a clause that could not be read,
     * since which clauses are read turns on the values the path has named, and no way names one
     * the whole did not ({@link Predicates#eachWayOf}). A clause refuted without them is refuted in
     * each way as well. Whether the conditions leave a way at all was kept where they were taken
     * in ({@link Predicates#assumeCond}); what taking them apart here can still find is a way that
     * what was learned of the values since leaves nothing.
     *
     * <p>One condition at a time, in the order they are held, and every one of them taken apart
     * while the copies allow. Nothing passes a condition over for looking as though it could not
     * matter: what a part says may be a relation between values none of whose bounds it moves, as
     * {@code x >= y || x == y} says of {@code x - y}, and the only answer to whether it changes
     * what the clauses come to is the verdict under it.
     *
     * <p>A way nothing enters is no value built and is not judged. The ways that are left are
     * combined as the arms of a split are ({@link Judgment#of}): a clause holds where it holds in
     * every one of them and is refuted where every one refutes it.
     *
     * <p>Each way entered is this construction judged again under what it knows, which is a copy of
     * the reading the walk made here, and it is counted with the copies the walk has made already
     * ({@link ContextMultiplicity}); a condition only one of whose ways is entered copies nothing.
     * A condition whose ways would compound past that is not taken apart, and nor is any condition
     * after it on this way. What is answered then is the verdict without them: a judgment made of
     * the ways that were taken apart and not the others would be a proof over some of the values.
     * Which conditions the copies reach is the order they are held in, as it is for any bound on
     * a search.
     */
    private Judgment verdictOf(TypeSymbol.AtModule named, Map<BindingId, Core> given, Known k,
                               Denotations at, boolean decidesFalse, ContextMultiplicity copies) {
        return takenApart(named, given, k, at, decidesFalse, copies,
                judging(named, given, k, at, decidesFalse), Set.of());
    }

    /** The same, where {@code whole} is what the construction came to under {@code k} as it
     * stands, and {@code apart} the conditions {@code k} holds that it already holds a part of. */
    private Judgment takenApart(TypeSymbol.AtModule named, Map<BindingId, Core> given, Known k,
                                Denotations at, boolean decidesFalse, ContextMultiplicity copies,
                                Judgment whole, Set<Known.OneOf> apart) {
        if (whole.verdict().holds()) {
            return whole;
        }
        for (Known.OneOf condition : k.heldAsOneOfTheirParts()) {
            if (apart.contains(condition)) {
                continue;
            }
            List<Known> entered = predicates.eachWayOf(condition, k).stream()
                    .filter(way -> !predicates.leavesNoRun(way))
                    .toList();
            if (entered.isEmpty()) {
                return null;
            }
            ContextMultiplicity opened = copies.opening(entered.size());
            if (opened == null) {
                return whole;
            }
            Set<Known.OneOf> further = new HashSet<>(apart);
            further.add(condition);
            Judgment together = null;
            for (Known way : entered) {
                Judgment here = takenApart(named, given, way, at, decidesFalse, opened,
                        judging(named, given, way, at, decidesFalse), further);
                if (here != null) {
                    together = together == null ? here : Judgment.of(together, here);
                }
            }
            return together;
        }
        return whole;
    }

    /** Which of the values a construction hands over is not one a clause may be read against
     * ({@link Terms#reportableSite}) — by identity, since it is these very values that stand in the clause. */
    private Set<Core> unnamed(Collection<Core> given, Known k, Denotations at) {
        Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
        for (Core value : given) {
            if (terms.reportableSite(value, at, k) == null) {
                out.add(value);
            }
        }
        return out;
    }

    /** The discharge verdict for a construction of {@code type} whose fields are being given
     * {@code given}, under {@code k} as it stands. */
    private Judgment judging(TypeSymbol.AtModule named, Map<BindingId, Core> given, Known k,
                             Denotations at, boolean decidesFalse) {
        // What the construction hands over that no clause may be read against. A clause naming one of
        // them is left to the run-time check, and one that is decided outright is still decided: what
        // cannot be guarded is not the same as what cannot be computed.
        Set<Core> unnamed = unnamed(given.values(), k, at);
        List<Owing> owed = new ArrayList<>();
        // Every clause that was read, in the order it was declared, and what was proved about it.
        // Every clause, whether or not the author named it: what a diagnostic can say about one is
        // the clause's to answer, and a clause left out of here because it could not be named is a
        // clause nothing downstream can point at either. One entry per clause, so no clause can be
        // on two sides of this at once.
        SequencedMap<Clause.Id, Judged> found = new LinkedHashMap<>();
        boolean refutedAlone = false;
        // Whether any clause is unsettled, which is not the same as whether any named one is: a
        // clause MAY be written without a name, and one that was is still a clause the guards did
        // not establish. Reading the answer off the names alone made an unnamed clause discharge.
        boolean unknown = false;
        // A clause the check cannot read here owes nothing and proves nothing, and the two are not
        // the same answer. Kept apart: a clause that owes nothing because it folded to what it is read
        // with is discharged, and one that owes nothing because nothing here could be asked of it is
        // left to the run-time check.
        boolean unreadable = false;
        // Which clauses may still hold wherever the value is built, each part of each read: a part
        // folding the way it is read holds, and one carried holds where what it owes is settled
        // below. A clause with no part read, or with a part read as nothing, holds nowhere this
        // says, and neither does a clause the declaration writes and this did not state.
        Map<Clause.Id, Boolean> holding = new LinkedHashMap<>();
        // A newtype construction from a value written out is the constant check's to report: it names
        // the clause that failed. It reads the construction as written, so a name given the value is
        // not one it sees, and this check says it instead — which is what `decidesFalse` carries.
        // The clauses that state something here, and not whether they are all of them: a clause
        // stating nothing readable at this construction is one the run-time check stands for, which
        // is what `unreadable` below already carries for the ones that were read.
        for (Clauses.Stated stated : clauses.statedAt(named, given).clauses()) {
            holding.merge(stated.clause().id(), !stated.parts().isEmpty(), Boolean::logicalAnd);
            for (Clauses.StatedPart part : stated.parts()) {
                Predicates.Owed o =
                        predicates.obligations(part.expr(), k, at, unnamed, decidesFalse);
                unreadable |= o.unreadable();
                holding.merge(stated.clause().id(), o.folded() == Predicates.Fold.HOLDS
                        || (o.folded() != Predicates.Fold.FAILS && !o.parts().isEmpty()
                                && !o.unreadable()), Boolean::logicalAnd);
                for (Predicates.Part eachOne : o.parts()) {
                    if (!(eachOne instanceof Predicates.Part.Carried carriedOne)) {
                        continue;
                    }
                    owed.add(new Owing(stated, carriedOne.clause()));
                }
            }
        }
        if (owed.isEmpty()) {
            return new Judgment(unreadable ? Verdict.UNREPRESENTABLE : Verdict.PROVED,
                    ClauseJudgments.of(found), held(holding));
        }
        // What the clauses are decided by, which is one half of what the reading can reach. The
        // other half is what the domain speaks of, and that is the domain's own to answer.
        Set<FactSubject> asked = new LinkedHashSet<>();
        for (Owing owing : owed) {
            asked.addAll(owing.owed().atomsItIsDecidedBy());
        }
        NumericDomain<FactSubject> dom = readingOf(k.numbers(), asked);
        // The same clauses read against the same site, under what would be known here had no
        // condition on the path settled anything. What each clause states of the sizes it names holds
        // either way, so both readings take it. Made where a clause is refuted and nowhere else:
        // which of the two readings refutes it is the one question this answers, and a construction
        // with no clause refuted would pay for a second reading nobody reads.
        NumericDomain<FactSubject> alone = null;
        // An invariant is the conjunction of its clauses, so every one of them is read before what
        // the invariant came out as is decided. A clause the values alone refute is the whole
        // invariant refuted on the values alone, whatever another clause needed to be refuted —
        // stopping at the first refutation would answer with whichever clause was declared first.
        boolean alongside = false;
        for (Owing owing : owed) {
            Predicates.Clause c = owing.owed();
            ClauseStatus status = statusOf(c, dom, k, owing.clause());
            if (status == ClauseStatus.REFUTED) {
                if (alone == null) {
                    alone = readingOf(k.unguarded().numbers(), asked);
                }
                if (c.refutedByTheValuesAlone(alone, k.unguarded().facts())) {
                    refutedAlone = true;
                }
                alongside = true;
            } else if (status == ClauseStatus.UNKNOWN) {
                unknown = true;
            }
            if (status != ClauseStatus.SETTLED) {
                holding.put(owing.clause().id(), false);
            }
            put(found, owing.clause(), status);
        }
        // Every clause that could be read and is discharged leaves the invariant proven, except where
        // one could not be read and still stands.
        Verdict verdict = refutedAlone ? Verdict.REFUTED_ALONE
                : alongside ? Verdict.REFUTED_NOT_ALONE
                : unknown ? Verdict.UNKNOWN
                : unreadable ? Verdict.UNREPRESENTABLE : Verdict.PROVED;
        return new Judgment(verdict, ClauseJudgments.of(found), held(holding));
    }

    /** The clauses {@code holding} says hold. */
    private static Set<Clause.Id> held(Map<Clause.Id, Boolean> holding) {
        Set<Clause.Id> out = new LinkedHashSet<>();
        holding.forEach((clause, holds) -> {
            if (holds) {
                out.add(clause);
            }
        });
        return out;
    }

    /**
     * The domain clauses decided by {@code asked} are read against, built from what {@code base}
     * holds.
     *
     * <p>Two steps that are one operation, and both are inside {@link DerivedNumericFacts}: what
     * every value the reading can reach carries is taken as holding, and then what follows about the
     * arithmetic the domain cannot carry — a product of two values, a truncating quotient — is
     * derived from what the reading proves of the values it was computed from. The second reads the
     * first, so the order is not a caller's to keep and cannot be: a reading is made by the one
     * function that makes one ({@link DerivedNumericFacts#readingOf}).
     *
     * <p>Each reading answers with its own. A bound derived here is derived from what this reading
     * assumed, so it belongs to the reading and not to the value — which is why the construction's
     * two readings are built by two calls rather than sharing one domain.
     */
    private NumericDomain<FactSubject> readingOf(NumericDomain<FactSubject> base,
                                                 Set<FactSubject> asked) {
        return DerivedNumericFacts.refine(base, terms, asked);
    }

    /**
     * What was proved about one clause where the value is built.
     *
     * <p>Established and refused are asked for separately and are not each other's negation, so
     * asking one of them and reading the other off it is what puts a clause the check merely could
     * not decide among the ones a value fails. A clause that comes out both is neither: it says the
     * two questions were answered against a reading that proves everything, and a check that filed
     * it under either answer would report a clause the value does not fail, or leave one it does.
     */
    private static ClauseStatus statusOf(Predicates.Clause owed, NumericDomain<FactSubject> dom, Known k,
                                         Clause.Ref clause) {
        boolean established = owed.dischargedBy(dom, k.facts());
        boolean refused = owed.refutedBy(dom, k.facts());
        if (established && refused) {
            throw new Clause.NotOneClause("clause " + clause.id()
                    + " is established and refused by what is known where it is built");
        }
        if (established) {
            return ClauseStatus.SETTLED;
        }
        return refused ? ClauseStatus.REFUTED : ClauseStatus.UNKNOWN;
    }

    /** Records what was proved about {@code clause}, joining it with what is already there for it:
     * one clause reached twice — through two spreads, or read again under a rewrite — is one
     * clause. */
    private static void put(SequencedMap<Clause.Id, Judged> found, Clause.Ref clause,
                            ClauseStatus status) {
        found.merge(clause.id(), new Judged(clause, status), Judged::merge);
    }

    /** Whether the constant check reads this construction: a newtype's, over a value written where
     * it is built. That check names the clause that failed, so it is left to say it — and it reads
     * the construction as written, so a name given the value is not one it sees. */
    private boolean constantlyBuilt(TypeSymbol.AtModule type, Core.Construct nd) {
        return newtypes.of(type.key()) && Terms.isWritten(nd.values().get(0).value());
    }

    /** One obligation and the clause it was owed by. */
    private record Owing(Clauses.Stated from, Predicates.Clause owed) {

        /** The clause this was owed by: which one it is and what a sentence may call it. Neither is
         * read here — this hands the clause on whole, so that a site choosing what to say asks it
         * rather than being handed one of its answers. */
        Clause.Ref clause() {
            return from.clause();
        }
    }
}
