package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.function.Function;

/**
 * One reading of one declaration, and everything that reading alone decides.
 *
 * <p>What a reading comes to is one thing and the answers derived from it are another, and the two
 * used to be held apart: the reading was handed on and each reader worked the answers out again.
 * Held together, whoever is handed the reading is handed what was made of it, and a question that
 * costs a reading of the declaration is put once however many readers put it.
 *
 * <p><b>Whether this is the declaration's canonical reading is not asked here.</b> A canonical one
 * is kept by a lender and handed to every question that reaches the declaration; one made with
 * something settled or something left out belongs to the question that asked for it and to nothing
 * else. Which of the two is being made is decided where a reading is asked for
 * ({@link InvariantChecker#readFields}), and this holds either the same way — so nothing derived
 * from a reading has to work out which kind it came from before it can be kept.
 *
 * <p>Not a value and not thread-safe on its own. What it holds is named by identity, and it is
 * owned by the store that lends it, whose walk is what its one thread is doing ({@link
 * LentReadings}). What is derived here is confined the same way and by the same owner.
 */
public final class DeclarationReading {

    /**
     * The declaration this is a reading of: the one its terms are bound under.
     *
     * <p>Not always the declaration a question asked about. A name that writes nothing, worn over
     * another that writes nothing, is lent this one's reading ({@link DeclarationReadings#ownerOf}),
     * and what is derived here is derived under this declaration whichever of them asked first.
     */
    private final TypeSymbol.AtModule owner;

    private final InvariantChecker.Seeded seeded;

    /** What the rules leave the declaration's fields able to hold, made when the first question
     *  asks for it. Null until then, and the same object afterwards. */
    private FieldDomains fields;

    private DeclarationReading(TypeSymbol.AtModule owner, InvariantChecker.Seeded seeded) {
        this.owner = owner;
        this.seeded = seeded;
    }

    /** The reading {@code seeded} of {@code owner} is, with nothing derived from it yet. */
    static DeclarationReading of(TypeSymbol.AtModule owner, InvariantChecker.Seeded seeded) {
        return new DeclarationReading(owner, seeded);
    }

    /** The declaration this is a reading of. */
    TypeSymbol.AtModule owner() {
        return owner;
    }

    /** The reading itself: what the clauses came to, as the seeding left them. */
    public InvariantChecker.Seeded seeded() {
        return seeded;
    }

    /**
     * What this reading leaves the declaration's fields able to hold, worked out by {@code derive}
     * where nothing has yet.
     *
     * <p>Derived from the reading and from nothing the asker brings, which is what lets the answer
     * outlive the question that first wanted it. The ends a conjunct moved are read by asking what
     * the rules leave without it, and each of those is a reading of the declaration — so a second
     * asker working them out again pays the whole attribution a second time.
     */
    FieldDomains fields(Function<InvariantChecker.Seeded, FieldDomains> derive) {
        FieldDomains had = fields;
        if (had != null) {
            return had;
        }
        FieldDomains made = derive.apply(seeded);
        fields = made;
        return made;
    }
}
