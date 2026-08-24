package souther.compiler.check;

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
    static List<OperationFacts.Declared> bindAll(List<OperationFacts.Declared> declared) {
        List<OperationFacts.Declared> visited = new ArrayList<>();
        for (OperationFacts.Declared each : declared) {
            // No default. A kind of fact added is a kind this has to say how to hold, rather than
            // one that passes through unchecked because nothing here mentions it.
            switch (each.fact()) {
                case OperationFact.AnswersItsArgument answers ->
                        DischargeRules.holdToTheDeclaration(each.operation(), answers.argument(),
                                null, Question::isANumber,
                                "the argument whose number the result is");
                // Both arguments, because which is the greater and which the lesser are one
                // statement and a signature could disagree with either half.
                case OperationFact.StatesTheOrderOfItsArguments states -> {
                    DischargeRules.holdToTheDeclaration(each.operation(), states.order().greater(),
                            null, type -> true, "the argument a positive answer names as greater");
                    DischargeRules.holdToTheDeclaration(each.operation(), states.order().lesser(),
                            null, type -> true, "the argument a positive answer names as lesser");
                }
                case OperationFact.ShiftsBy shifts -> DischargeRules.holdShift(each.operation(),
                        shifts);
                case OperationFact.BoundsItsResult bounded ->
                        DischargeRules.holdBound(each.operation(), bounded.bound());
                case OperationFact.BuildsItsResultFrom builds ->
                        DischargeRules.holdToTheDeclaration(each.operation(),
                                builds.built().from(),
                                new souther.compiler.semantics.ArgumentRef.TheContainer(),
                                Question::holdsElements,
                                "the container something is built from");
                case OperationFact.ResultIsNoSmallerThan bounded ->
                        DischargeRules.holdToTheDeclaration(each.operation(), bounded.container(),
                                new souther.compiler.semantics.ArgumentRef.TheContainer(),
                                Question::holdsElements,
                                "a container the result is no smaller than");
                case OperationFact.ReadsItsContainer reads ->
                        DischargeRules.holdToTheDeclaration(each.operation(), reads.container(),
                                new souther.compiler.semantics.ArgumentRef.TheContainer(),
                                Question::holdsElements,
                                "the container a predicate reads");
                case OperationFact.IsStatedOverAProjection over ->
                        DischargeRules.holdToTheDeclaration(each.operation(), over.projection(),
                                new souther.compiler.semantics.ArgumentRef.TheClosure(),
                                type -> type instanceof souther.compiler.types.Type.FnOf,
                                "the projection a predicate is stated over");
                // Neither names an argument, so there is nothing about one to hold to a signature.
                // What holds them to the library is the question they answer for
                // ({@link Question}), which asks of the declaration whether the operation is one
                // the question is even about.
                case OperationFact.StatesItsPredicateOfEveryElement _,
                     OperationFact.MeansTheSameAsASizeOfNought _ -> { }
                case OperationFact.ComputesANumber computes ->
                        DischargeRules.holdNumericResult(each.operation(), computes.result());
                case OperationFact.IsDefinedByCases defined ->
                        DischargeRules.holdCase(each.operation(), defined.one());
            }
            visited.add(each);
        }
        return visited;
    }

    /** The same, over what the language declares. */
    static List<OperationFacts.Declared> bindAll() {
        return bindAll(OperationFacts.declarations());
    }

    private OperationFactBinder() {}
}
