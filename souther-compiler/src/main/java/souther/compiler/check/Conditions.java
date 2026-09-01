package souther.compiler.check;

import souther.compiler.semantics.PositiveOrder;
import souther.compiler.core.Core;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.NumericDomain.LinearForm;
import souther.compiler.numeric.NumericDomain.Rel;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.ConstantArguments;
import souther.compiler.semantics.ResultRange;
import souther.compiler.types.BinOp;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * What a condition states, read off the condition and nothing else.
 *
 * <p>The half of reading a guard that no path is involved in. Two questions were one here for as
 * long as one reader asked both: what a condition <em>says</em> — which comparison it is once the
 * six ways of writing one are read as one, what an emptiness check means, which relation an order
 * operation states — and what saying it makes <em>known</em> on the path it was written on. The
 * first is a function of the condition and the names around it; the second needs what the path had
 * already established. {@link Predicates} keeps the second and asks this for the first.
 *
 * <p>Which is what lets the answer be recorded. A relation a condition states is the same relation
 * wherever it is read, so it may stand beside a recipe ({@link Derivation.Chosen}) where a range
 * could not — and an arm read under what chose it is read against a domain the arm's own reader
 * holds, out of relations recorded here.
 *
 * <p>Functions and not an object. Nothing here has state or a lifetime, and {@link Terms} is passed
 * where a name has to be read rather than held: a reader this one could be given at construction is
 * a reader something has to remember to give it, and the naming of an expression is reached from
 * places that have no {@link Predicates} to hand ({@link ContractDischarge}).
 */
final class Conditions {

    private Conditions() {}

    /**
     * What choosing the arm {@code decidedBy} states of the values around it, as relations.
     *
     * <p>Only what holds by that arm being the answer, and only what holds on its own. A condition
     * asserted true states each of its conjuncts; asserted false it states the disjunction of their
     * denials, which is not a list of relations, so it states none of them and this answers with
     * nothing. Under-answering costs precision and over-answering is unsound, so where the shape
     * runs out this stops — which is the opposite way round from what a recipe declares it may read
     * ({@link Derivation.Chosen.Arm}), and worth keeping straight.
     *
     * <p>A case and an attempt state nothing here. What choosing them settles is what the value's
     * type guarantees of what the arm binds, which is a declaration's answer and not a relation a
     * condition wrote, so it is read through the one reading of a declaration there is
     * ({@link TypeGuarantees}) and composed with this beside the arm ({@link Terms#chosen}).
     *
     * <p>An operation the library defines by cases states the relations its case is reached under,
     * which arrive already lowered to the values the call was given ({@link Choice}). Nothing about
     * the operation is asked here, and nothing about it needs to be.
     *
     * <p>Written as a switch over {@link Choice.Decides} with an arm for every way of deciding. As an
     * {@code instanceof} it answered "nothing is settled" for every way it had not been told about,
     * which is the same silence a new producer would want to be stopped by: a value that is one of
     * several would get its arms and lose what chose between them, and be bounded by their span with
     * no arm ruled out.
     *
     * <p><b>What the values a condition names guarantee is not here either, and the walk has it.</b>
     * {@link Predicates#assumeCond} takes {@link Predicates#sizeFacts} and
     * {@link Predicates#resultFacts} into what is known before it reads the condition at all: a size
     * is at or above nought whether the condition holds or not, so those are guarantees about values
     * and not statements the condition makes. An arm read here is read without them, so
     * {@code List.size(xs)} under {@code not List.isEmpty(xs)} comes to "not nought" here where the
     * walk has "above nought". Not two readings of one question — it is one question this reader
     * does not ask. It was written down as the same family as what a case and an attempt rest on,
     * and it is not: a value built through a checked constructor carries what its declaration
     * states ({@link TypeGuarantees}), and a list carries a length that is never negative because of
     * what a length is, with no declaration saying so. A third source, and #988.
     */
    static List<NumericConstraint> settledBy(Terms terms, Choice.Decides decidedBy, Denotations at) {
        List<NumericConstraint> out = new ArrayList<>();
        switch (decidedBy) {
            case Choice.Decides.ACondition(Core cond, boolean holding) ->
                    stating(terms, cond, at, holding, out);
            case Choice.Decides.ByArgumentRelations(List<Choice.ArgumentRelation> relations) ->
                    standing(terms, relations, at, out);
            // A case and an attempt state nothing here. What choosing them settles is what the
            // value's type guarantees of what the arm binds, which is a guarantee about a place
            // rather than a relation, and it is read where places are seeded (#982). Written as arms
            // of this switch and not left to a default: what a way of deciding settles is a question
            // somebody has to answer, and "nothing" is an answer rather than the absence of one.
            case Choice.Decides.ACase ignored -> { }
            case Choice.Decides.ItWasBuilt ignored -> { }
            case Choice.Decides.ItDeparted ignored -> { }
        }
        return out;
    }

    /**
     * The relations the arguments of a library definition's case stand in, as constraints.
     *
     * <p>Already relations when they arrive ({@link Choice.ArgumentRelation}), so what is left is
     * reading each side as a form. A side no form is read of — an argument that is the answer of
     * something nothing names — states nothing and is left out.
     *
     * <p>Which is one answer for both readers of these arms, and it has to be. Dropping a relation
     * leaves the arm reachable where it is not: a recipe then spans an answer it need not have
     * ({@link DerivedNumericFacts}), and a clause read case by case is then asked to hold in a case
     * the values cannot reach ({@link Predicates.Piecewise}). Both directions cost precision and
     * neither states anything the values fail, which is the rule the class doc gives — and it is why
     * this is decided here rather than by each reader, where the two could come to degrade
     * differently and nothing would say which of them was reading the same choice.
     */
    private static void standing(Terms terms, List<Choice.ArgumentRelation> relations,
                                 Denotations at, List<NumericConstraint> out) {
        for (Choice.ArgumentRelation one : relations) {
            LinearForm<FactSubject> left = terms.affineOf(one.left(), at);
            LinearForm<FactSubject> right = terms.affineOf(one.right(), at);
            if (left != null && right != null) {
                out.add(new NumericConstraint(left.minus(right), one.rel()));
            }
        }
    }

    /**
     * The relations {@code cond}, asserted with polarity {@code positive}, states on its own.
     *
     * <p>Read through the same normalisations a guard is: an emptiness check is the comparison it
     * means, an order operation compared against zero is the comparison of what it orders, and a
     * negation is the condition under it with the polarity turned over. Without them the six ways of
     * writing one comparison are six conditions, and what an arm states would depend on which of
     * them an author wrote.
     *
     * <p>A conjunction asserted true states both halves, and a disjunction asserted false states
     * both denied. Anything else with two halves states neither: one of them holds and this cannot
     * say which.
     */
    static void stating(Terms terms, Core rawCond, Denotations at, boolean positive,
                        List<NumericConstraint> out) {
        Core cond = asSizeComparison(rawCond);
        Core ordered = asOrderComparison(terms, cond, at);
        if (ordered != cond) {
            stating(terms, ordered, at, positive, out);
        }
        Restated under = restated(cond);
        if (under != null) {
            stating(terms, under.condition(), at, under.denied() != positive, out);
            return;
        }
        if (cond instanceof Core.Binary b
                && ConditionJoin.of(b.op()).map(join -> join.under(positive)).orElse(null)
                        == ConditionJoin.BOTH) {
            stating(terms, b.left(), at, positive, out);
            stating(terms, b.right(), at, positive, out);
            return;
        }
        if (cond instanceof Core.Binary b) {
            ComparisonClaim placed = Comparison.of(b).map(Comparison::claim).orElse(null);
            LinearForm<FactSubject> left = placed == null ? null : terms.affineOf(b.left(), at);
            LinearForm<FactSubject> right = placed == null ? null : terms.affineOf(b.right(), at);
            if (left != null && right != null) {
                // Asserted false, what the condition states is what holds where it does not.
                out.add(new NumericConstraint(left.minus(right),
                        (positive ? placed : placed.denied()).statedRelation()));
            }
        }
    }

    /**
     * A comparison of what an operation answering an order answered, as the comparison of the two
     * values it orders — or {@code e} unchanged.
     *
     * <p>What such an operation answers is a sign ({@link DischargeRules#orderStatedBy}), so a
     * condition that settles which side of nought the answer falls on is a condition about the two
     * arguments. One account: the relation is the one the sign is left standing to nought, taken
     * between the argument a positive answer says is the greater and the other one, so the six
     * relations and the two sides of the comparison are all read from the row the library's
     * operation has rather than from a case for each.
     *
     * <p><b>Which side of nought is worked out and not matched.</b> This read a written zero, on the
     * reasoning that a sign compared with anything else bounds how far the answer is from nought
     * rather than saying which way it falls. That stopped being true the day the comparisons were
     * declared to answer one of three numbers: {@code Int.compare(a, b) >= 1} leaves the answer at
     * one, and {@code > -1} leaves it at nought or one, and both settle a side. Read by the shape of
     * what was written, the two canonical facts about one operation — the order it states and where
     * its answer runs — could not be put together, which is the division this whole change is about
     * (#1016). So the condition and the declared bounds are composed, and what the composition
     * leaves is asked which way it stands.
     *
     * <p>And only where both values are ones this check can name. The sign is a number the domain
     * carries whatever it is the order of, so a comparison of two values it cannot name is less than
     * what it already had: a clause reading {@code daysBetween(acquiredOn, lostOn) >= 0} is a bound
     * on that count, and rewriting it into a comparison of two dates the check cannot relate would
     * leave the clause unreadable — a construction dropped from the check where it had been reported.
     * Reading a predicate never takes a reading away.
     */
    static Core asOrderComparison(Terms terms, Core e, Denotations at) {
        if (!(e instanceof Core.Binary b)) {
            return e;
        }
        ComparisonClaim placed = Comparison.of(b).map(Comparison::claim).orElse(null);
        if (placed == null) {
            return e;
        }
        boolean callFirst = b.left() instanceof Core.PreservedCall;
        Core side = callFirst ? b.left() : b.right();
        Core against = callFirst ? b.right() : b.left();
        if (!(side instanceof Core.PreservedCall call) || call.args().size() != 2) {
            return e;
        }
        PositiveOrder positive =
                DischargeRules.orderStatedBy(call.operation());
        if (positive == null
                || terms.bodyKey(call.args().get(0), at) == null
                || terms.bodyKey(call.args().get(1), at) == null) {
            return e;
        }
        // The relation the source wrote, read from the sign's side of the comparison: `call rel x`
        // however the two were written round.
        Rel written = (callFirst ? placed : placed.turned()).statedRelation();
        Rel stands = standsToNought(terms, call, written, against, at);
        return stands == null ? e
                : comparison(ComparisonWriting.operatorStating(stands),
                        CallArguments.of(positive.greater(), call),
                        CallArguments.of(positive.lesser(), call), b);
    }

    /**
     * Which way {@code call}'s answer stands to nought, given that a condition puts it {@code rel}
     * what {@code against} reads as — or null where that leaves both sides open.
     *
     * <p>Composed in the numeric domain rather than decided here, so that what a step is worth is
     * the step the domain knows about: over whole numbers {@code > -1} is {@code >= 0}, and this
     * would either have to say so a second time or answer as though a sign could fall between the
     * two. The rules taken in are the two there are — what the operation declares of its answer
     * ({@code semantics}) and what the condition says — and the tightest relation to nought the two
     * prove together is the answer.
     *
     * <p>The number the condition stands against is read and not matched, for the reason every
     * argument a fact names is: a name given a constant is that constant, so {@code compare(a, b) >
     * zero} under {@code let zero = 0} is the condition it looks like.
     *
     * <p>Nothing where the two leave both sides open, and nothing where they leave nothing at all: a
     * condition no answer satisfies states no order, and that the arm is never entered is said by
     * what reads reachability rather than by an order nobody can stand on.
     */
    private static Rel standsToNought(Terms terms, Core.PreservedCall call, Rel rel, Core against,
                                      Denotations at) {
        LinearForm<FactSubject> read = terms.affineOf(against, at);
        if (rel == null || read == null || !read.coefs().isEmpty()) {
            return null;
        }
        // One atom, standing for the number this call answered. Nothing else is in this domain: what
        // is asked is what the operation and the condition prove between them, and a rule about
        // anything else would be a rule about a value that is not the sign.
        Object sign = new Object();
        java.util.Map<Object, Granularity> spacing =
                java.util.Map.of(sign, terms.granularityOf(call.type()));
        LinearForm<Object> answered = LinearForm.atom(sign);
        NumericDomain<Object> known = NumericDomain.<Object>top()
                .assuming(sign, ResultRange.of(call.operation(), ConstantArguments.NONE), spacing)
                .assume(answered.minus(LinearForm.constant(read.constant())), rel, spacing);
        if (known.isBottom()) {
            return null;
        }
        // Tightest first: a sign held at nought is an equality and not two half-statements, and one
        // held above it says more than one held at or above it.
        for (Rel each : List.of(Rel.EQ, Rel.GT, Rel.LT, Rel.GE, Rel.LE, Rel.NE)) {
            if (known.entails(answered, each)) {
                return each;
            }
        }
        return null;
    }

    /** An emptiness check as the comparison it means, or {@code e} unchanged. */
    static Core asSizeComparison(Core e) {
        if (e instanceof Core.PreservedCall call && call.args().size() == 1
                && DischargeRules.sizeMeantBy(call.operation()) != null) {
            Core size = new Core.PreservedCall(DischargeRules.sizeMeantBy(call.operation()),
                    call.args(), Type.INT, call.pos());
            return new Core.Binary(BinOp.EQ, size, new Core.Int(0, Type.INT, call.pos()),
                    CoverageOrigin.unwritten(), Type.BOOL, call.pos());
        }
        return e;
    }

    record Polar(Core expr, boolean positive) {}

    /**
     * {@code e}, asserted with polarity {@code positive}, as the comparison of {@code ==} or {@code <}
     * that says the same thing: {@code a /= b} is {@code a == b} denied, {@code a >= b} is
     * {@code a < b} denied, and {@code a > b} is {@code b < a}. A fact is settled by key equality, so
     * without this the six ways to compare two terms are six facts, and a guard written one way would
     * leave a clause written the other unsettled.
     */
    static Polar polar(Core e, boolean positive) {
        if (e instanceof Core.Binary b) {
            ComparisonClaim placed = Comparison.of(b).map(Comparison::claim).orElse(null);
            if (placed != null) {
                return canonical(b, placed, positive);
            }
        }
        return new Polar(e, positive);
    }

    /**
     * The one of the two canonical comparisons {@code placed} is, and which way it is asserted.
     *
     * <p>Which of the two it is, which side of it each value goes on and whether it is denied are
     * what {@code placed} states ({@link ComparisonClaim#canonical}). What is here is the rest:
     * that a canonical comparison of this compiler's own is written as an operator between the two
     * sides, and that its denial is carried by the polarity beside it rather than by a node.
     */
    private static Polar canonical(Core.Binary b, ComparisonClaim placed, boolean positive) {
        AsPolar as = new AsPolar(b);
        Polar stated = placed.canonical(b.left(), b.right()).expressedAs(as);
        return positive ? stated : as.denied(stated);
    }

    /**
     * A canonical comparison, written as a node standing where {@code of} did with what is asserted
     * of it held beside it.
     *
     * <p>{@code of} is here because a node is more than its two sides and its operator: where it
     * came from, what it answers and where it stands are what the readings below it file the fact
     * under, and a comparison put in its place that said any of them differently would be a fact
     * about somewhere else. What is written is the reader's own business and is no part of what the
     * comparison states, which is why the node is held here and not carried in the statement.
     */
    private record AsPolar(Core.Binary of)
            implements CanonicalComparison.Expression<Core, Polar> {

        @Override
        public Polar theSameValue(Core left, Core right) {
            return new Polar(comparison(BinOp.EQ, left, right, of), true);
        }

        @Override
        public Polar below(Core left, Core right) {
            return new Polar(comparison(BinOp.LT, left, right, of), true);
        }

        /** Carried beside the node, which is what a polarity is for: a denial written as a node
         *  would be a second shape for the readings below to take apart before they could read the
         *  comparison under it. */
        @Override
        public Polar denied(Polar statement) {
            return new Polar(statement.expr(), !statement.positive());
        }
    }

    static Core.Binary comparison(BinOp op, Core left, Core right, Core.Binary of) {
        return new Core.Binary(op, left, right, of.origin(), of.type(), of.pos());
    }

    /**
     * One condition written in terms of another, and whether it states it or denies it.
     *
     * <p>What every walk over a clause carries is a pair — the part being read and whether the
     * denials above it came out even — and this is the step that pair is moved by. Written as
     * "what a negation is applied to", the step could only ever flip, so the ways of stating a
     * condition without flipping were not steps at all and a walk stopped at them.
     *
     * @param condition what is written under, which the walk goes on with
     * @param denied    whether holding this one is denying that one
     */
    record Restated(Core condition, boolean denied) {}

    /**
     * What {@code e} is written in terms of, or {@code null} where it is written in terms of
     * nothing.
     *
     * <p>Four spellings of a denial and two of an assertion, read as one thing. {@code Bool.not} is
     * an ordinary helper: the analysis representation keeps it as a call, and a clause read off an
     * imported declaration is the body it expands to — {@code if b then false else true} over a
     * binding holding the argument. A comparison against a written {@code true} or {@code false} is
     * the sixth: {@code p == false} and {@code p /= true} deny what {@code p} states, and the other
     * two state it.
     *
     * <p>The equivalence class and not the spellings. What a reader below is given is an atom and a
     * polarity, so {@code not (p == false)} and {@code p} arrive as the same pair — and a reader
     * that learned one spelling at a time would answer for the ones somebody had got to.
     */
    static Restated restated(Core e) {
        if (e instanceof Core.PreservedCall call && call.operation().equals(DischargeRules.NOT)
                && call.args().size() == 1) {
            return new Restated(call.args().get(0), true);
        }
        if (e instanceof Core.LetIn li) {
            Restated inner = restated(li.body());
            return inner != null && inner.denied()
                    && inner.condition() instanceof Core.Read r
                    && r.binding().equals(li.binder().binding())
                    ? new Restated(li.value(), true) : null;
        }
        if (e instanceof Core.If iff
                && iff.then() instanceof Core.Bool t && !t.value()
                && iff.els() instanceof Core.Bool f && f.value()) {
            return new Restated(iff.cond(), true);
        }
        return againstATruthValue(e);
    }

    /**
     * The same of a comparison one side of which is a written {@code true} or {@code false}.
     *
     * <p>Whether it denies is whether the two disagree: an equality against {@code true} and a
     * disequality against {@code false} state what the other side states, and the other pair deny
     * it. Read off the operator and the literal rather than written out as four cases, so a fifth
     * way to write the same thing arrives here as one of the two answers and not as a case nobody
     * added.
     */
    private static Restated againstATruthValue(Core e) {
        if (!(e instanceof Core.Binary bin)
                || (bin.op() != BinOp.EQ && bin.op() != BinOp.NE)) {
            return null;
        }
        boolean holds = bin.op() == BinOp.EQ;
        if (bin.right() instanceof Core.Bool truth) {
            return new Restated(bin.left(), truth.value() != holds);
        }
        return bin.left() instanceof Core.Bool truth
                ? new Restated(bin.right(), truth.value() != holds) : null;
    }

}
