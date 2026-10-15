package souther.compiler.check;

import souther.compiler.types.Type;
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
 * <p>Except where nothing is written under any name supposed. A reading stopping at a name with no
 * rule under it leaves no rule unread and says nothing of the stop, which is what reading on would
 * have come to as well; so a supposing only stops a reading at the names with something under them,
 * and one with none of those reads every declaration as itself and is lent its own reading. What a
 * count takes to have values is the whole supposing all the same.
 *
 * <p>Made once for a supposing and kept while it lasts. A count asks one declaration's rules three
 * questions each time it reads the declaration, and reads it again each round of a rising; what the
 * rules leave is the same every time the supposing is the same, so it is read once. And a newtype
 * that writes nothing, worn over another that writes nothing, is read as the one beneath, as its
 * own reading is ({@link DeclarationReadings#ownerOf}) — up to the first name the reading stops at.
 * A ring of such names has no reading beneath to take until something in it stops a reading; once
 * something does, it is a chain, and read once rather than once per name with the rest of the chain
 * under each.
 *
 * <p>Not a value and not shared. What it keeps was read in one world, and it is made where that
 * world is to hand and dropped when the count that made it is done.
 */
final class Supposing {

    /** Nothing supposed: every declaration is read as itself, and its reading is lent. */
    static final Supposing NOTHING = new Supposing(Set.of(), Set.of(), null);

    private final Set<TypeSymbol> names;
    /** What this shares with the other supposings of its count; null for {@link #NOTHING}. */
    private final Across across;
    /** The names a reading stops at: those of {@link #names} with a rule somewhere under them. */
    private final Set<TypeSymbol> stopping;
    private final InvariantChecker.Reach reach;
    private final Map<TypeSymbol.AtModule, TypeSymbol.AtModule> owners = new HashMap<>();
    /** The names a walk found round a ring, or on the way into one, each read as itself. */
    private final Set<TypeSymbol.AtModule> unshared = new HashSet<>();
    private final Map<TypeSymbol.AtModule, DeclarationReading> made = new HashMap<>();

    private Supposing(Set<TypeSymbol> names, Set<TypeSymbol> stopping, Across across) {
        this.names = Set.copyOf(names);
        this.stopping = Set.copyOf(stopping);
        this.reach = InvariantChecker.Reach.stoppingAt(this.stopping);
        this.across = across;
    }

    /**
     * {@code names} supposed to have values, with nothing read under it yet, a reading stopping
     * at the ones {@code across} says have a rule under them.
     */
    static Supposing of(Set<TypeSymbol> names, Across across) {
        if (names.isEmpty()) {
            return NOTHING;
        }
        Set<TypeSymbol> stopping = new LinkedHashSet<>();
        for (TypeSymbol each : names) {
            if (across.under(each)) {
                stopping.add(each);
            }
        }
        return new Supposing(names, stopping, across);
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
     * <p>Where no reading stops anywhere, the declaration's own reading, lent as it is to everyone
     * else — through what the supposings of one count share, where there are others to share
     * with.
     */
    DeclarationReading readingOf(TypeSymbol.AtModule named, RuleReadingContext reading) {
        if (stopping.isEmpty()) {
            return across == null
                    ? InvariantChecker.readFields(named, reading, Map.of(), reach)
                    : across.ownReadingOf(named, reading);
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
     * {@link DeclarationReadings#wornOverWritingNothing} answers lead to before one a reading stops
     * at, or {@code named} itself where they go round a ring.
     *
     * <p>Every name passed over is answered with the same owner, so a chain is walked once
     * however many of its names are asked about.
     */
    private TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule named, RuleReadingSource source) {
        if (stopping.contains(named)) {
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
            if (beneath == null || stopping.contains(beneath)) {
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

    /**
     * What every supposing one count makes has in common: which names have a rule under them, and
     * the declarations' own readings, for the supposings that stop nowhere.
     *
     * <p>Kept here and not by a supposing, because a search supposes the same names over and over
     * and both answers are about the declarations and not about what is supposed. Made for one
     * question of the store and dropped with it: a reading lent here was recorded as read by that
     * question when it was first borrowed, and borrowing it again for the same question would
     * record the same reads again.
     */
    static final class Across {

        private final RuleReadingSource source;
        private final Map<TypeSymbol.AtModule, PublishedRules> governing = new HashMap<>();
        private final Map<TypeSymbol, Boolean> known = new HashMap<>();
        private final Map<TypeSymbol.AtModule, DeclarationReading> own = new HashMap<>();

        Across(RuleReadingSource source) {
            this.source = source;
        }

        /** {@code named}'s own reading in {@code reading}, borrowed once. */
        DeclarationReading ownReadingOf(TypeSymbol.AtModule named, RuleReadingContext reading) {
            DeclarationReading had = own.get(named);
            if (had != null) {
                return had;
            }
            DeclarationReading read = InvariantChecker.readFields(named, reading, Map.of(),
                    InvariantChecker.Reach.EVERYTHING);
            own.put(named, read);
            return read;
        }

        /**
         * Whether a rule is written at or anywhere under {@code name}.
         *
         * <p>What a stop asks ({@link TypeGuarantees#anyRuleUnder}), with a declaration some of
         * whose rules never arrived counted as writing one: a reading that stops above it may be
         * leaving a rule unread, and whether it is is not something to decide here.
         */
        boolean under(TypeSymbol name) {
            Boolean had = known.get(name);
            if (had != null) {
                return had;
            }
            boolean any = TypeGuarantees.anyRuleUnder(new Type.Ref(name), source, owner -> {
                PublishedRules rules =
                        PublishedRules.governing(owner, source.published(), governing);
                return !rules.reached().isEmpty() || !rules.everyRuleReached();
            });
            known.put(name, any);
            return any;
        }
    }
}
