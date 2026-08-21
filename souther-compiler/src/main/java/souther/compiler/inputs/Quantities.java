package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;

import java.util.Map;
import java.util.Optional;

/**
 * What the rules leave a quantity taken over several of a behavior's input positions.
 *
 * <p><b>The relational half of {@link InputDomain}.</b> A {@link Position} answers about itself, and
 * a rule can be about no position in particular: {@code x + y <= 5} relates two of them and divides
 * neither. Asked a position at a time, that rule leaves each of them running from none to five and
 * the pair coming to ten — and a border drawn at eight is a border on a quantity the model never
 * arrives at, whose rows are rows nobody can write. A product of per-position answers cannot carry a
 * relation, so what a caller with a form in hand asks is asked here.
 *
 * <p><b>Knowledge, not search.</b> Nothing here decides where a row goes or how long to look for
 * one. What it answers is what the declarations reaching this input leave a quantity, and what they
 * leave once some positions are fixed — which is the same rule set read again rather than a second
 * reading of it. How a search uses that, when it gives up, and what it concludes from having given
 * up are the search's, and keeping them apart is why a quantity added later costs nothing here.
 *
 * <p><b>Reached through {@link InputDomain} and nowhere else, and never wider than a position.</b>
 * What is answered is the declarations reaching this input, intersected with what each of its terms
 * guarantees of itself, intersected with whatever has been fixed. So an answer here is at least as
 * tight as the box of the positions it is over, and a border can go away for being asked about
 * properly and can never appear.
 *
 * <p><b>Whose positions.</b> A term is queryable where its path is one of this input's. Which
 * numbers a path is measured at is not settled once and for all by the reading of the declarations:
 * a bare list nothing bounds becomes an axis about its length where a body measures it, and that
 * term is a term of this input as much as the ones the declarations named. A term at a path this
 * input does not have is a caller's mistake and is refused as one — read as an emptiness it would be
 * a bug wearing the words of a contradiction in the model.
 *
 * <p><b>Across parameters, a product is the answer rather than a gap.</b> Rules reach this input
 * from the declarations of its parameters and from nowhere else: one reading per parameter, and
 * nothing a body writes reaches any of them. Two parameters are therefore related by nothing, and a
 * form spanning both is answered by solving each parameter's part of it against that parameter's
 * rules and adding the results — the parts stay forms, and only the answers are added. A day when a
 * behavior's own clauses relate its parameters is the day that composition has to change, and it is
 * the only place it does.
 */
public sealed interface Quantities permits ReadQuantities {

    /**
     * Where the values of {@code form} run, or null at either end where nothing bounds them.
     *
     * <p>The form as the rule wrote it, over this input's terms. What it comes to is asked of the
     * relations that reach its positions rather than composed from what each of them projects.
     */
    NumericDomain.Bounds runsBetween(NumericDomain.LinearForm<NumericTerm> form);

    /**
     * The same, of one term.
     *
     * <p>The one-term case of the question above and not a second answer to it. Two derivations of
     * one answer is what this layer exists to stop, and a form over one position is a form.
     */
    default NumericDomain.Bounds runsBetween(NumericTerm term) {
        return runsBetween(NumericDomain.LinearForm.atom(term));
    }

    /**
     * The same rules, with these positions fixed at these values.
     *
     * <p>A refinement of what is asked and not a new reading. Fixing accumulates, so a caller that
     * fixes one position and then another is asking about both together — and asking about both
     * together is all that is asked, whatever order they arrived in and whatever was asked on the
     * way. Where a fixing contradicts what is already held, what comes back proves it
     * ({@link #emptiness}) rather than answering as though nothing had been said.
     */
    Quantities given(Map<NumericTerm, Count> fixed);

    /** The same, of one position. */
    default Quantities given(NumericTerm term, Count fixed) {
        return given(Map.of(term, fixed));
    }

    /**
     * Why the rules leave no value under what is fixed, or empty where nothing proved they leave
     * none.
     *
     * <p>Empty is not "there is a value". A search reading it that way would take the absence of a
     * proof for the presence of one, which is the difference between a branch it may close and a
     * branch it has not finished.
     */
    Optional<EmptyInput> emptiness();
}
