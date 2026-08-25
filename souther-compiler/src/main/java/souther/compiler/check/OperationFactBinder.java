package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;

import java.util.ArrayList;
import java.util.List;

/**
 * Holds what is declared of the language's operations to what the library declares.
 *
 * <p>A fact names an argument of an operation, and what an operation's arguments are is the
 * library's to say. Where the two disagree there is nothing to be done at a call — the fact is
 * about an argument that is not there, or is not the kind of thing the fact is about — so it is
 * said before any call is read rather than met as a missing answer at whichever reader arrives
 * first.
 *
 * <p><b>Over the declarations and not over what a reader asked for.</b> Bound one fact at a time as
 * it was looked up, a fact nothing looked up was a fact nothing checked, and how much of the
 * declaration was validated depended on which consumers a compilation happened to have. This walks
 * the whole list, so a fact declared is a fact held to the library whether or not anything reads
 * it.
 *
 * <p><b>And bound, not merely visited.</b> A fact is not held to the library because its kind was
 * reached: the operation it is declared of is resolved against the library for every declaration,
 * outside the switch. Held inside it, the resolution was reached only by the kinds that name an
 * argument — the ones whose arm calls {@link DischargeRules#holdToTheDeclaration} — so a kind that
 * names none passed through an empty arm having been held to nothing. Whether a declaration was
 * checked depended on what its fact happened to mention, and the next kind of fact would have lost
 * the same way on the day its arm was written empty.
 *
 * <p>Here and not with the declarations, because holding them takes the library's signatures and
 * the questions this check asks of a type — which is this side's, and is what the declarations were
 * given a home away from.
 *
 * <p>Read on the first ask, as {@link Combinators} and {@link Preserved} are: what this requires of
 * the library is required of a check that reads these facts, and a checker that reads none must not
 * be held to it.
 */
final class OperationFactBinder {

    /**
     * Holds every fact of {@code declared} to the library, and answers with the ones it visited.
     *
     * <p>The source is a parameter so that what this covers can be asked of it with a source of
     * one's own. Reading {@link OperationFacts#declarations()} directly, a test could show that the
     * facts there are valid and not that a fact added later would be visited at all.
     */
    static List<OperationFacts.Declared> bindAll(Stdlib stdlib,
                                                List<OperationFacts.Declared> declared) {
        List<OperationFacts.Declared> visited = new ArrayList<>();
        for (OperationFacts.Declared each : declared) {
            // Before the switch and outside it, so that being declared is what holds a fact to the
            // library rather than being a kind that happens to name an argument. An arm below with
            // nothing in it then says what it means — there is nothing to check beyond the
            // operation — instead of standing for a declaration nothing looked at.
            DischargeRules.holdTheOperationToTheLibrary(stdlib, each.operation());
            // No default. A kind of fact added is a kind this has to say how to hold, rather than
            // one that passes through unchecked because nothing here mentions it.
            switch (each.fact()) {
                case OperationFact.AnswersAFormOfItsArguments answers ->
                        DischargeRules.holdAFormOfItsArguments(stdlib, each.operation(), answers.form());
                // Both arguments, because which is the greater and which the lesser are one
                // statement and a signature could disagree with either half.
                case OperationFact.StatesTheOrderOfItsArguments states -> {
                    DischargeRules.holdToTheDeclaration(stdlib, each.operation(), states.order().greater(),
                            null, TypeRequirement.ANY,
                            "the argument a positive answer names as greater");
                    DischargeRules.holdToTheDeclaration(stdlib, each.operation(), states.order().lesser(),
                            null, TypeRequirement.ANY,
                            "the argument a positive answer names as lesser");
                }
                case OperationFact.ShiftsBy shifts -> DischargeRules.holdShift(stdlib, each.operation(),
                        shifts);
                case OperationFact.BoundsItsResult bounded ->
                        DischargeRules.holdBound(stdlib, each.operation(), bounded.bound());
                case OperationFact.BuildsItsResultFrom builds ->
                        DischargeRules.holdToTheDeclaration(stdlib, each.operation(),
                                builds.built().from(),
                                new ArgumentRef.TheContainer(),
                                TypeRequirement.CONTAINER,
                                "the container something is built from");
                case OperationFact.ResultIsNoSmallerThan bounded ->
                        DischargeRules.holdToTheDeclaration(stdlib, each.operation(), bounded.container(),
                                new ArgumentRef.TheContainer(),
                                TypeRequirement.CONTAINER,
                                "a container the result is no smaller than");
                case OperationFact.ReadsItsContainer reads ->
                        DischargeRules.holdToTheDeclaration(stdlib, each.operation(), reads.container(),
                                new ArgumentRef.TheContainer(),
                                TypeRequirement.CONTAINER,
                                "the container a predicate reads");
                case OperationFact.IsStatedOverAProjection over ->
                        DischargeRules.holdToTheDeclaration(stdlib, each.operation(), over.projection(),
                                new ArgumentRef.TheClosure(),
                                TypeRequirement.CLOSURE,
                                "the projection a predicate is stated over");
                // None of these names an argument — a silence names none by definition — so there
                // is nothing about one to hold to a signature. Their operation is held above with
                // every other, which is what makes this arm a statement about these facts rather
                // than a gap.
                case OperationFact.StatesItsPredicateOfEveryElement _,
                     OperationFact.MeansTheSameAsASizeOfNought _,
                     OperationFact.SaysNothingOf _ -> { }
                // Stated of the number an operation answers, so an operation that answers none is
                // one the proposition is not about. Waved through, it was a fact anything could
                // carry — which is what an arm that does nothing promises, and the promise is
                // wrong here (#1027).
                case OperationFact.EveryAnswerItCanGiveHasASourceValue _ ->
                        DischargeRules.holdTheResultToTheDeclaration(stdlib, each.operation(),
                                TypeRequirement.NUMBER,
                                "what every answer of it has a value for");
                case OperationFact.AnswersANumberTakenOfTheOneValueItIsGiven taken ->
                        DischargeRules.holdTakenOf(stdlib, declared, each.operation(), taken.how());
                case OperationFact.ComputesANumber computes ->
                        DischargeRules.holdNumericResult(stdlib, each.operation(), computes.result());
                case OperationFact.IsDefinedByCases defined ->
                        DischargeRules.holdCase(stdlib, each.operation(), defined.one());
            }
            visited.add(each);
        }
        return visited;
    }

    /** The same, over what the language declares. */
    static List<OperationFacts.Declared> bindAll(Stdlib stdlib) {
        return bindAll(stdlib, OperationFacts.declarations());
    }

    private OperationFactBinder() {}
}
