package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import souther.compiler.revision.StoreWork;
import souther.compiler.values.StringMachineAnswers;

import java.util.function.Supplier;

/**
 * Where a reading of a declaration gets what somebody has already made of the declaration.
 *
 * <p>Two things, for two lifetimes. The answers about a declaration's string machines
 * ({@link #of}) are borrowed from the store's own answer for the declaration, which outlives an
 * edit that leaves the declaration's clauses as they were. The declaration's canonical reading
 * ({@link #reading}) — its rules read whole, with nothing settled and nothing left out — is handed
 * on for the revision it was made in and no longer: it is not a value, so no store answer holds it,
 * and what makes handing it on sound is that within one revision every world it could be read from
 * is the same world.
 *
 * <p>What is shared there is work rather than an answer, and it is shared with the reads it was
 * made by: a question of the store is kept by what it read, so one handed a reading and nothing
 * else would hold an answer made from rules it does not depend on ({@link StoreWork}).
 *
 * <p>A capability and not a value, either way. What comes back from {@link #of} is the thing a
 * reading asks as it goes ({@link StringMachineAnswers}), so this is made where a store is to hand,
 * passed along with the reading, and never kept in anything a store answers with. A reading that
 * holds nothing to ask is given {@link #NONE} and works everything out itself.
 */
@FunctionalInterface
public interface DeclarationReadings {

    /** The answers for a reading of {@code declaration}'s string machines. */
    StringMachineAnswers of(TypeKey declaration);

    /**
     * What the revision this lends under has worked out.
     *
     * <p>Beside the two above and on a lifetime of its own, because it is about neither a
     * declaration nor a reading: every answer it holds is settled by the work it answers and the
     * allowance that work mints for itself ({@link RevisionWork}). One capability whatever the work
     * is, so that a reader rebuilding a lender hands the whole of what the revision knows on with
     * one call, and a kind of work added later is nothing such a reader has to hear about. A
     * reading with no revision behind it has {@link RevisionKnowledge#NONE} and does every piece
     * of work it meets.
     */
    default RevisionKnowledge revision() {
        return RevisionKnowledge.NONE;
    }

    /**
     * The declaration's canonical reading as the source {@code origin} names and {@code policy}
     * decide it: the one somebody has already made under those terms, or the one {@code read} makes,
     * kept for whoever asks next. A lender that keeps none does the reading every time.
     *
     * <p>Borrowing and making are one act because what is shared is one thing. A reading is work,
     * and the work was done by reading what the store answers; a question handed the result read
     * none of that itself, so it is recorded as having read what the making read
     * ({@link StoreWork}). Handed the result alone it would be kept over an edit to what the making
     * read, and would answer about rules the author has since changed.
     *
     * <p>All three terms, because all three decide what the reading comes to. A policy is what a
     * reading may spend, and a reading made under other terms is another reading. A source is where
     * the clauses are read from and what the names in them mean: a reader may hand over one that
     * answers for fewer clauses than the store holds — a count asking what it would come to without
     * one declaration's rules does exactly that — and what comes back is a reading of what that
     * source left, which is not the declaration's own. Which source it is, is what its origin says
     * ({@link RuleReadingSource.Origin}), so that is what is handed here and not the source.
     */
    default DeclarationReading reading(TypeSymbol.AtModule declaration,
                                       RuleReadingSource.Origin origin, ReadingPolicy policy,
                                       Supplier<InvariantChecker.Seeded> read) {
        return DeclarationReading.of(declaration, read.get());
    }

    /**
     * Whose canonical reading {@code declaration}'s is: the declaration itself, or the name
     * beneath it whose reading is the same reading.
     *
     * <p>A newtype that writes nothing, worn over another newtype that writes nothing, adds nothing
     * a reading reads: its value is the same location as the value beneath, no rule of its own is
     * read there, and the walk goes on into the same names. So its reading is the one beneath, and
     * a chain of such names is read once rather than once per name with the whole chain under each.
     * Only that edge: a name worn over one that writes rules reads them as a walk reaches them, and
     * the name beneath reads them as its own, which are two readings.
     *
     * <p>Answered by whoever answers for the compilation's declarations, and here by the
     * declaration itself. A lender with nothing to ask shares nothing, which is the reading every
     * declaration has of its own.
     */
    default TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule declaration) {
        return declaration;
    }

    /**
     * The newtype {@code named} is worn over, where both of them write nothing; null where either
     * writes something or {@code named} is worn over anything else.
     *
     * <p>One edge of what {@link #ownerOf} follows, and the only edge: a reading of {@code named}
     * is the reading of what this answers. Asked of what each declaration publishes and of what
     * it wraps, in that order, so a reader whose answers are kept by what they read depends on the
     * declaration beneath only where the one above writes nothing.
     */
    static TypeSymbol.AtModule wornOverWritingNothing(TypeKey named,
                                                      PublishedDeclarations published,
                                                      NewtypeInners inners) {
        if (!writesNothing(published.of(named))) {
            return null;
        }
        return inners.of(named) instanceof Type.Ref ref
                && ref.name() instanceof TypeSymbol.AtModule beneath
                && writesNothing(published.of(beneath.key()))
                ? beneath : null;
    }

    /**
     * Whether {@code declared} is a newtype that adds nothing a reading reads: no clause of its own
     * and nothing spread into it.
     *
     * <p>Asked of what the declaration publishes and of nothing a reading made. A clause nobody
     * could work out is published as one all the same, and a declaration whose meaning could not be
     * read is not one that says nothing — so neither is taken for a name that writes nothing.
     */
    private static boolean writesNothing(PublishedDeclarationResult declared) {
        return declared instanceof PublishedDeclarationResult.Found(
                        DeclarationMeaning.Product product)
                && product.newtype() && product.includes().isEmpty()
                && product.clauses().isEmpty();
    }

    /**
     * The same for the reader whose answer the reading is: it makes one and is lent none.
     *
     * <p>The answer being made is the one there would be to lend, and what the making watches is
     * what the answer comes to hold — so a reading lent to it would leave the answer holding
     * nothing. What it makes is kept, because it is the declaration's canonical reading and the
     * question that asked for the answer is the next to want it.
     */
    default DeclarationReading readingForAnAnswer(TypeSymbol.AtModule declaration,
                                                  RuleReadingSource.Origin origin,
                                                  ReadingPolicy policy,
                                                  Supplier<InvariantChecker.Seeded> read) {
        return DeclarationReading.of(declaration, read.get());
    }

    /**
     * What a reading borrows while the answer about {@code named}'s machines is being made:
     * nothing, and what it makes is kept here afterwards.
     *
     * <p>Nothing, because the answer being made is the one there would be to borrow. The
     * declaration's own machines are {@code recorder}, so that what the reading builds is what the
     * answer comes to hold; every other declaration's are worked out by the reading itself, since
     * asking for another declaration's answer from inside this one is how two declarations that
     * reach each other come to wait on each other. Worked out and kept: a reading of one of those
     * is a reading like any other, and what it comes to is what its own counterfactual is handed.
     *
     * <p>Worked out is not walked again. Where the sets those readings meet were found to stop is
     * the revision's ({@link #revision}), and a set two declarations both reach is walked for the
     * first of them — which is a fact about the set and about no declaration, so neither reading
     * comes to anything it would not have come to alone.
     *
     * <p>And what it makes is kept, because the reading that answer is made by is the declaration's
     * canonical reading: the question that asked for the answer is the next to want it, and is
     * handed this rather than making a second beside it.
     */
    default DeclarationReadings whileTheAnswerIsMade(TypeKey named, StringMachineAnswers recorder) {
        DeclarationReadings lender = this;
        return new DeclarationReadings() {

            @Override
            public StringMachineAnswers of(TypeKey declaration) {
                return declaration.equals(named)
                        ? recorder : StringMachineAnswers.unborrowed(lender.revision());
            }

            @Override
            public RevisionKnowledge revision() {
                return lender.revision();
            }

            @Override
            public TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule declaration) {
                return lender.ownerOf(declaration);
            }

            @Override
            public DeclarationReading reading(TypeSymbol.AtModule declaration,
                                              RuleReadingSource.Origin origin,
                                              ReadingPolicy policy,
                                              Supplier<InvariantChecker.Seeded> read) {
                return lender.readingForAnAnswer(declaration, origin, policy, read);
            }

            @Override
            public DeclarationReading readingForAnAnswer(TypeSymbol.AtModule declaration,
                                                         RuleReadingSource.Origin origin,
                                                         ReadingPolicy policy,
                                                         Supplier<InvariantChecker.Seeded> read) {
                return lender.readingForAnAnswer(declaration, origin, policy, read);
            }
        };
    }

    /**
     * Nothing to borrow, for a reading with no store to ask.
     *
     * <p>Named where it is wanted and never arrived at by leaving an argument out. Reading a
     * declaration for oneself where somebody has already read it is not a slower way to the same
     * answer — it is the whole of what a reading costs, paid again — so which readers do that is a
     * thing said in the source rather than a consequence of which overload was to hand.
     *
     * <p>A reading's own answers all the same, and a fresh one at each asking: a reading that
     * borrows nothing still comes to the machines it built, and what it came to is what its own
     * counterfactual is handed. Handing out one shared object would make every such reading write
     * into the same maps.
     */
    DeclarationReadings NONE = _ -> StringMachineAnswers.unborrowed(RevisionKnowledge.NONE);
}
