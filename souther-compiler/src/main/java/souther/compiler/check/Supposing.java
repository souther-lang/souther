package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The declarations a count takes to have values whatever their rules say, and the readings made
 * under that supposing.
 *
 * <p>The two together because a reading is what the supposing decides. A name supposed to have a
 * value is not read — not its own rules and nothing under it — so a declaration's rules read under
 * one supposing are another reading than its own, and are made here rather than lent by whoever
 * keeps the declaration's own reading.
 *
 * <p>Made once for a supposing and kept while it lasts. A count asks one declaration's rules three
 * questions each time it reads the declaration, and reads it again each round of a rising; what the
 * rules leave is the same every time the supposing is the same, so it is read once. And a newtype
 * that writes nothing, worn over another that writes nothing, is read as the one beneath, as its
 * own reading is ({@link DeclarationReadings#ownerOf}) — up to the first name supposed to have a
 * value, where a reading stops. A ring of such names has no reading beneath to take until something
 * in it is supposed; once something is, it is a chain, and read once rather than once per name with
 * the rest of the chain under each.
 *
 * <p>Not a value and not shared. What it keeps was read in one world, and it is made where that
 * world is to hand and dropped when the count that made it is done.
 */
final class Supposing {

    /** Nothing supposed: every declaration is read as itself, and its reading is lent. */
    static final Supposing NOTHING = new Supposing(Set.of());

    private final Set<TypeSymbol> names;
    private final InvariantChecker.Reach reach;
    private final Map<TypeSymbol.AtModule, TypeSymbol.AtModule> owners = new HashMap<>();
    /** The names a walk found round a ring, or on the way into one, each read as itself. */
    private final Set<TypeSymbol.AtModule> unshared = new HashSet<>();
    private final Map<TypeSymbol.AtModule, DeclarationReading> made = new HashMap<>();

    private Supposing(Set<TypeSymbol> names) {
        this.names = Set.copyOf(names);
        this.reach = InvariantChecker.Reach.stoppingAt(this.names);
    }

    /** {@code names} supposed to have values, with nothing read under it yet. */
    static Supposing of(Set<TypeSymbol> names) {
        return names.isEmpty() ? NOTHING : new Supposing(names);
    }

    /** Whether {@code name} is supposed to have a value. */
    boolean contains(TypeSymbol name) {
        return names.contains(name);
    }

    /** How far a reading under this supposing goes at each name it meets. */
    InvariantChecker.Reach reach() {
        return reach;
    }

    /**
     * The rules of {@code named} as they read under this supposing, in {@code reading}.
     *
     * <p>Where nothing is supposed, the declaration's own reading, lent as it is to everyone else.
     */
    DeclarationReading readingOf(TypeSymbol.AtModule named, RuleReadingContext reading) {
        if (names.isEmpty()) {
            return InvariantChecker.readFields(named, reading, Map.of(), reach);
        }
        TypeSymbol.AtModule owner = reading.source().origin() instanceof AModulesRules
                ? ownerOf(named, reading.source()) : named;
        DeclarationReading had = made.get(owner);
        if (had != null) {
            return had;
        }
        DeclarationReading read = InvariantChecker.readFields(owner, reading, Map.of(), reach);
        made.put(owner, read);
        return read;
    }

    /**
     * Whose reading {@code named}'s is under this supposing: the last name the edges
     * {@link DeclarationReadings#wornOverWritingNothing} answers lead to before one supposed to
     * have a value, or {@code named} itself where they go round a ring.
     *
     * <p>Every name passed over is answered with the same owner, so a chain is walked once
     * however many of its names are asked about.
     */
    private TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule named, RuleReadingSource source) {
        if (names.contains(named)) {
            return named;
        }
        Set<TypeSymbol.AtModule> walked = new LinkedHashSet<>();
        TypeSymbol.AtModule at = named;
        TypeSymbol.AtModule owner;
        while (true) {
            if (unshared.contains(at) || !walked.add(at)) {
                // Round a ring nothing supposed breaks, or into one: no reading beneath is any of
                // these, and a walk reaching one of them later is in the same place.
                unshared.addAll(walked);
                return named;
            }
            TypeSymbol.AtModule known = owners.get(at);
            if (known != null) {
                owner = known;
                break;
            }
            TypeSymbol.AtModule beneath = DeclarationReadings.wornOverWritingNothing(
                    at.key(), source.published(), source.inners());
            if (beneath == null || names.contains(beneath)) {
                owner = at;
                break;
            }
            at = beneath;
        }
        for (TypeSymbol.AtModule each : walked) {
            owners.put(each, owner);
        }
        return owner;
    }
}
