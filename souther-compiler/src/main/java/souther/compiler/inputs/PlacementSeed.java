package souther.compiler.inputs;

import souther.compiler.check.FieldDomains;
import souther.compiler.check.Owed;
import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;

/**
 * What a rule placed, taken apart into where it was written and what it says there.
 *
 * <p>The four things a rule writes carry a name in four spellings — a term of an axis, a term a
 * comparison drew, a coordinate a clause placed an end on, a position a clause admits values at —
 * and each was read where it was met. Reading a name is not one of the four questions: which number
 * of a location a rule is about and which values may stand there are what differs between them, and
 * where the location is is the same question every time. Split here, so that one reading of a name
 * answers all four and each keeps its own meaning.
 *
 * <p><b>The split, and not a type over the four.</b> A rule about the length of a string and a rule
 * about which values it may hold are not one kind of statement, and nothing here makes them one:
 * what is common is the address, and {@link Placed} is what is left of each once the address is out
 * of it.
 *
 * <p><b>A seed and not yet a filing.</b> Where the address stands is a separate answer, taken
 * against what the walk observed ({@link NameReach}) — a name written at a sum stands under each of
 * its cases, so one of these becomes a filing at each of them. Nothing here says where, and nothing
 * here says a name reached nowhere.
 */
public record PlacementSeed(RuleAddress address, Placed placed, RuleRef by, RuleCitation cited) {

    public PlacementSeed {
        if (address == null || placed == null) {
            throw new IllegalArgumentException("a rule placed something somewhere");
        }
        if (by == null || cited == null) {
            throw new IllegalArgumentException(
                    "and it was some rule that placed it, which a reader can be sent to look at");
        }
    }

    /**
     * What a rule says at an address, once where it says it is out of it.
     *
     * <p>Two, because a rule about a location says one of two things: something about a number of
     * what stands there, or something about which values may stand there. Which of them it is comes
     * from the rule and is never read off the other.
     */
    public sealed interface Placed {

        /**
         * About one number of what stands at the address.
         *
         * <p>Which number is carried and not derived. A {@code String} is measured on its own order
         * and on its length, so two rules at one address can be about two numbers, and a reader that
         * took the number from the location would file both under whichever it guessed.
         */
        record ANumberOfIt(FieldDomains.CoordinateKind which) implements Placed {

            public ANumberOfIt {
                if (which == null) {
                    throw new IllegalArgumentException("a number of a location is some number of it");
                }
            }
        }

        /** About which values may stand at the address, which is not a number of them. */
        record TheValuesThere() implements Placed {}
    }

    /**
     * The seed for a term, read as a rule of the value at {@code root} — null where no rule of that
     * value names it.
     *
     * <p>Exhaustive over {@link NumericTerm}, with no {@code default}: a term of a third kind is a
     * name this would have to read, and stopping the compile is what says so.
     */
    public static PlacementSeed of(TermPath root, NumericTerm term, RuleRef by,
                                   RuleCitation cited) {
        RuleAddress address = RuleAddress.of(root, term.path());
        if (address == null) {
            return null;
        }
        return new PlacementSeed(address, new Placed.ANumberOfIt(switch (term) {
            case NumericTerm.ValueOf _ -> new FieldDomains.CoordinateKind.OfItsOwnValue();
            case NumericTerm.TakenOf taken ->
                    new FieldDomains.CoordinateKind.OfWhatAnOperationAnswers(taken.operation());
        }), by, cited);
    }

    /**
     * The seed for a question one rule of the value at {@code root} raised.
     *
     * <p>Exhaustive over {@link Owed}, with no {@code default}. The two arms are the two things a
     * rule says at a location, and they are the two here for the same reason.
     *
     * <p><b>One rule and one question, and never a field something was said about.</b> Two clauses
     * narrowing one field are two placements: dropping either leaves the field narrowed and the
     * other standing, so an account keyed on the field is one a rule can go missing from without
     * anything to see. What tells them apart is the rule, so the rule is carried.
     */
    public static PlacementSeed of(TermPath root, Owed owed, RuleRef by, RuleCitation cited) {
        return switch (owed) {
            case Owed.AdmittedValues values ->
                    new PlacementSeed(new RuleAddress(root, values.path()),
                            new Placed.TheValuesThere(), by, cited);
            case Owed.Boundary boundary ->
                    new PlacementSeed(new RuleAddress(root, boundary.on().path()),
                            new Placed.ANumberOfIt(boundary.on().kind()), by, cited);
        };
    }
}
