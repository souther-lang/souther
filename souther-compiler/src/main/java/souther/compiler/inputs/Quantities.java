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
 * <p><b>Reached through {@link InputDomain} and nowhere else, and never wider than a term's own.</b>
 * A form is added up out of parts, and a part is the finest unit a relation survives in: the terms
 * of one parameter the reading of its declarations has a coordinate for, and the terms it has none
 * for. What a part comes to is what its terms are on their own — where each stands if it has been
 * fixed, what its own position was read to hold, and what the term guarantees of itself — and,
 * where the reading can be asked at all, those facts solved together with the rules that relate
 * them and the form projected out of that. Parts are added, and adding only ever makes an answer
 * out of answers, so a border can go away for being asked about properly and can never appear.
 *
 * <p>Composed that way because neither meeting nor projecting distributes. Everything each term is
 * on its own, met against everything the relations leave the whole form, is wider than the sum of
 * the parts each met on its own — so one term the reading cannot name would take the rules relating
 * every other term of that parameter with it. And what the rules leave a form, met afterwards
 * against what each of its coordinates is known to be, is wider than what the rules and those facts
 * leave it together — so a rule holding two coordinates at one apiece says nothing as soon as a
 * third is one the rules leave unbounded. Both are the same mistake: an answer assembled at a
 * coarser unit than the facts are held at loses whichever fact the coarse mechanism has no room
 * for.
 *
 * <p><b>Whose positions, and owned is not the same as known about.</b> A term is queryable where
 * what it sits under is something this behavior takes. What the reading holds is what the
 * enumeration found and what the measurement named ({@link InputDemand}), and a term at one of those
 * is answered for like any other — the declarations reaching it relate it to everything they relate
 * any position to, which is how a clause of a type bounds an occurrence several links into a
 * recursive value. A term at a path the reading holds no position for is answered for as well, with
 * what it guarantees of itself and nothing the declarations relate it to. Which numbers a path is measured at is not
 * settled by that reading either: a bare list nothing bounds becomes an axis about its length where
 * a body measures it. What is refused is a term under something this behavior does not take, which
 * no reading of this input could ever answer for — read as an emptiness it would be a bug wearing
 * the words of a contradiction in the model. Whether a path names a field the type has is settled
 * where the term is made.
 *
 * <p><b>Across parameters, one space and not a product of them.</b> Rules reach this input from the
 * declarations of its parameters and from nowhere else: one reading per parameter, and nothing a
 * body writes reaches any of them. Two parameters are therefore related by nothing the declarations
 * say — which is a fact about what has been read and not a reason to keep the readings apart. They
 * are renamed into this input's own names and said together, so a form spanning both is answered by
 * projecting out of that one space rather than by adding up what each parameter's rules leave its
 * own part. Adding the parts is what a rule relating two of them cannot survive, and a day when
 * something does relate them — a condition a body wrote — is a day this needs no rearranging for.
 *
 * <p>Which is why nothing here asks a parameter whether anything is left. Every parameter's reading
 * is in that space, so a reading kept beside it could answer the same question over the same rules
 * renamed, and which of the two spoke would be settled by the order they were asked in — with the
 * one that cannot see across two parameters asked first.
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
     * Where a row may be written, before anything a body says is taken in.
     *
     * <p>The one way over to {@link SearchRegion}, and it is one way. What the declarations leave is
     * where the borders are read from, and a region is where a row for one of them is looked for —
     * so a caller may go from the first to the second and nothing can come back. Read the other way,
     * a region narrowed by the conditions on the way to one border would reach the reader that
     * decides which borders exist, and an obligation would go away for this compiler having read
     * more of the body.
     */
    SearchRegion region();

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
