package souther.compiler.inputs;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;

import java.util.Map;
import java.util.Optional;

/**
 * What the rules leave a quantity taken over several of a behavior's input positions, and what
 * order each of its terms is measured on.
 *
 * <p>The second because it is the same reading asked about one term rather than a form of them: what
 * a quantity runs between is read on the orders its terms are on, and a caller that took the orders
 * from somewhere else would be adding up numbers this reading counts differently.
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
 * fixed, where the values it is answered from leave it, and what the term guarantees of itself —
 * and, where the reading can be asked at all, those facts solved together with the rules that
 * relate them and the form projected out of that. Parts are added, and adding only ever makes an
 * answer out of answers, so a border can go away for being asked about properly and can never
 * appear.
 *
 * <p><b>Where a term's values come from is what says who answers for it, and there are two.</b> A
 * number one position answers is answered by that position's own reading. A number taken over a run
 * stands at no position, and is answered by what every value the run walks guarantees, put through
 * the step the operation repeats from the value it starts at. Read as one — as a position's answer,
 * because that was the only publisher there was — a total came back with nothing said about it, and
 * a border on it was owed a row at a value the model admits nothing at.
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
 *
 * <p><b>And one space per question and not one for the input, because a position exists under
 * conditions.</b> A field of a case is there where the value turned out to be that case, and a
 * field of an element where the sequence holds one — so a question naming such a position is asked
 * of the rows that meet those conditions, and the rules that reach it are the ones about those
 * rows. Every reading met into one space instead, the cases of a sum would be rules that hold
 * together, and one case its own rules refuse would refuse an input whose other cases are rows an
 * author can write.
 *
 * <p>What those conditions come to is part of what a question is answered against and not only part
 * of deciding whose rules to read: a question that names a position inside a container is a
 * question about rows whose container holds something, which is a fact the rules have a word for.
 *
 * <p>Which leaves {@link #emptiness} asking something no one context answers. Whether a value of
 * this input exists at all is quantified over the alternatives a value has — a sum has one wherever
 * any case does, a container that may be empty has one whatever it would hold — so it is a fold
 * over those and not a projection out of a space.
 */
public sealed interface Quantities permits ReadQuantities {

    /**
     * Both orders of {@code term} as this reading has it: the one a value at its position is read
     * on, and the one the number it names is answered on.
     *
     * <p><b>The answer for a term of this input, and the only thing that resolves where the term
     * sits.</b> Which order a term is measured on follows from what stands where its number comes
     * from, and where that is is settled once by the reading that made this. A caller working it
     * out from a type it holds is answering with whatever walk put that type in its hand — a walk
     * that follows a written value stops where a value is built, and a shared name of a sum is a
     * position a number is taken at and not a place a value is composed for.
     *
     * <p>Both ends together, because a term that is what an operation answered has two orders and a
     * caller handed one of them has whichever end the caller before it meant. The day the two part
     * is the day a row is decoded on a count the value is not written in.
     *
     * <p><b>And so that nothing derives it from an expression.</b> A rule is written beside
     * operands, and the type of an operand is not the type of the position the rule is about: an
     * operation the arithmetic rewrote into a form over two positions is compared as what it
     * answers with, so {@code Date.daysBetween(a, b) > 10} has {@code Int} on both sides and dates
     * at both positions. Read off the comparison, every position of that rule was written back as a
     * whole number and read off a row as one, and both directions agreed with each other and with
     * nothing else.
     *
     * <p><b>A term under no position of the reading still has an order.</b> The reading stops where
     * a path returns to a declaration already open on it, and it reports the end of a path the
     * measurement named rather than every step on the way; nothing stops a rule from naming what is
     * under either. What a report is about and what a declaration says are two questions, and only
     * the first of them stops there.
     */
    TermOrders ordersOf(NumericTerm term);

    /**
     * How many the rules leave the container standing at {@code at}, or every number where they
     * leave it unsaid.
     *
     * <p>Answered here because both halves of it are this reading's: which positions hold a
     * container is what the reading found, and what its rules leave one of them is what the same
     * reading says. Kept as a table beside a reading, a caller could ask what one reading's
     * containers come to under another's rules, and the answer would be about neither.
     *
     * <p>Counts of containers and nothing else. What this feeds is how many elements to build, so an
     * operation whose number is not how many the value holds has no business bounding it:
     * {@code Time.hour(t) <= 5} would otherwise be read as a container of at most five.
     *
     * <p>About the positions of the input and about nothing else, which is why it takes one rather
     * than a path. A coordinate of a construction plan is spelled with the same {@link TermPath} and
     * is a different thing: the plan goes on past where the reading stops, and puts positions under
     * a sum the declaration has none of. What a plan's node holds is read off that node's own type,
     * which is where its rules are — and a reading handed one of those answers that nothing here is
     * a position of it, rather than that no rule bounds it.
     */
    int mostHeldAt(PositionId at);

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
