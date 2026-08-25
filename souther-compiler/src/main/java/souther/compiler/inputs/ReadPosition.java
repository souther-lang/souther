package souther.compiler.inputs;

import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ProjectionEvidence;
import souther.compiler.check.TypeView;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.values.AdmissibleSet;

import java.util.List;

/**
 * The one reading of a position, and what it came to.
 *
 * <p>Package-private, so that {@link Position} is an answer and not a shape anything can fill in.
 * A public record is a constructor anything can call, and an artifact whose point is that it was
 * made once cannot be one.
 *
 * <p>The fields are what the reading saw on the way; {@link #reading} and {@link #obligations} are
 * what follows from them. Held together because they are one reading: copied apart, the day
 * somebody works out {@link #numericDomain} differently for a position that has distinctions is a
 * day the compiler contradicts itself about where the same values stop.
 *
 * @param declared what the position's type states before any rule was crossed with it, kept so that
 *                 a widening can hand it back and so that a distinction this position does not have
 *                 can be told from one the rules refused
 */
record ReadPosition(TermPath path, TypeView view, NumericTerm term,
                    NumericDomain.Bounds numericDomain, DeclaredBounds.Bounds ownEnds,
                    NumericDomain.Bounds narrowedEnds, NumericDomain.Bounds rangeLeft,
                    List<TypeSymbol> narrowedLower,
                    List<TypeSymbol> narrowedUpper, boolean nothingExists,
                    ProjectionEvidence projection, List<Case> declared, ReadingResult reading,
                    ObligationDomain obligations, AdmissibleSet.Completeness completeness,
                    BlockReason valuesUnread, List<UnreadRule> unreadRules,
                    List<StandingQuestion> unansweredQuestions, boolean rulesNotReached,
                    StructuralInspection structure) implements Position {

    ReadPosition {
        narrowedLower = List.copyOf(narrowedLower);
        narrowedUpper = List.copyOf(narrowedUpper);
        declared = List.copyOf(declared);
        unreadRules = List.copyOf(unreadRules);
        unansweredQuestions = List.copyOf(unansweredQuestions);
    }

    @Override
    public Type type() {
        return view.declared();
    }

    @Override
    public List<TypeSymbol> narrowedBy(boolean lower) {
        return lower ? narrowedLower : narrowedUpper;
    }

    /**
     * The widening first, because it makes the reading's own answer unusable.
     *
     * <p>Where the rules leave the position nothing, every distinction is refused and every one of
     * them is counted anyway. Read in the other order, that position would answer {@code Refused}
     * about a distinction a report is asking for a row at — the two halves of one position saying
     * opposite things, which is what putting the widening here is for.
     */
    @Override
    public Admits admissionOf(TypeSymbol leaf) {
        for (Case each : declared) {
            if (each instanceof Case.SumCase sum && sum.leaf().equals(leaf)) {
                return admissionOf(each);
            }
        }
        return new Admits.Unsettled(new Unsettlement.NoSuchDistinction());
    }

    @Override
    public Admits admissionOf(Case one) {
        if (obligations instanceof ObligationDomain.Conservative) {
            return new Admits.Unsettled(new Unsettlement.RulesLeaveNothing());
        }
        if (reading.refused().contains(one)) {
            return new Admits.Refused();
        }
        if (!reading.kept().contains(one)) {
            // Not a distinction this reading has. Nothing was read about it, which is a different
            // answer from the rules having refused it.
            return new Admits.Unsettled(new Unsettlement.NoSuchDistinction());
        }
        return switch (reading) {
            case ReadingResult.Complete _ -> new Admits.Admitted();
            case ReadingResult.NotSeparated _ ->
                    new Admits.Unsettled(new Unsettlement.AlternativesNotSeparated());
            case ReadingResult.Partial partial ->
                    new Admits.Unsettled(new Unsettlement.ReadingStopped(partial.why()));
            case ReadingResult.Unsupported unsupported ->
                    new Admits.Unsettled(new Unsettlement.ReadingStopped(unsupported.why()));
        };
    }
}
