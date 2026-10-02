package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.KnownExtents;
import souther.compiler.values.StringMachineAnswers;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading a supposing hands a declaration says what a reading of that declaration stopping at
 * every supposed name says, whichever reading it was handed.
 *
 * <p>A supposing hands out two readings that are not made for the declaration under it. One is the
 * reading of a newtype beneath, for a newtype that writes nothing worn over another — lent past a
 * name the reading should stop at, it would read the rules the supposing was about and say the
 * declaration has no value by them. The other is the declaration's own reading, where no name
 * supposed has a rule under it — and lent where one has, it would read those rules too. What the
 * readings say is compared rather than which they are, because that is what a count reads off them:
 * whether the rules leave anything, and what they leave at every place the declaration has.
 *
 * <p>Asked of every declaration under every one name supposed, in both orders, since what a
 * supposing lends depends on which name of a chain it read first.
 */
class AReadingUnderASupposingIsTheOneThatStopsThereTest {

    /**
     * A chain of names that write nothing over one whose rules leave it no value; a ring of such
     * names with one more worn over it; a ring of records with a rule under every one of them; a
     * ring of records with no rule anywhere; a record holding one of each beside a rule of its
     * own; and a record whose rule about a place deep in what it holds leaves nothing beside the
     * rule written there, and leaves something once that is not read.
     */
    private static final String MODULE = """
            module demo

            data Empty = Int
                invariant none = value >= 2 && value <= 1

            data X0 = Empty
            data X1 = X0
            data X2 = X1
            data X3 = X2

            data R1 = R2
            data R2 = R3
            data R3 = R1
            data Into = R1

            data P1 = { p: P3, k: Int }
                invariant k1 = k >= 1 && k <= 4
            data P2 = { p: P1 }
            data P3 = { p: P2, j: Int }
                invariant j3 = j >= 2 && j <= 3

            data Q1 = { q: Q2 }
            data Q2 = { q: Q1 }

            data Holds = { a: Q1, b: P2, n: Int }
                invariant n0 = n >= 0 && n <= 3

            data Outer = { b: P2 }
                invariant deep = b.p.k >= 5
            """;

    private static final List<String> NAMES = List.of("Empty", "X0", "X1", "X2", "X3", "R1",
            "R2", "R3", "Into", "P1", "P2", "P3", "Q1", "Q2", "Holds", "Outer");

    @Test
    void everyDeclarationIsLentWhatItsOwnReadingUnderTheSupposingSays() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        compilation.answerEverything();
        RuleReadingSource source = RuleReadings.of(compilation, "demo");
        RuleReadingContext reading = RuleReadingContext.of(source, ReadAs.THE_COMPILATION_DOES,
                compilation.db().readings());
        Supposing.Across rules = new Supposing.Across(source);
        List<String> backwards = new ArrayList<>(NAMES);
        Collections.reverse(backwards);
        int lentPastTheSupposing = 0;
        int lentItsOwn = 0;
        for (String supposed : NAMES) {
            InvariantChecker.Reach stopsThere =
                    InvariantChecker.Reach.stoppingAt(Set.of(declared(supposed)));
            for (List<String> order : List.of(NAMES, backwards)) {
                Supposing supposing = Supposing.of(Set.of(declared(supposed)), rules);
                for (String asked : order) {
                    if (asked.equals(supposed)) {
                        continue;
                    }
                    TypeSymbol.AtModule named = declared(asked);
                    DeclarationReading lent = supposing.readingOf(named, reading);
                    List<Object> own = saidBy(InvariantChecker.readFields(
                            named, reading, Map.of(), stopsThere), named, reading, stopsThere,
                            source);
                    assertEquals(own, saidBy(lent, named, reading, supposing.reach(), source),
                            () -> asked + " under " + supposed
                                    + " supposed was lent a reading that says something else");
                    if (own.get(0).equals(Optional.empty()) && asked.startsWith("X")) {
                        lentPastTheSupposing++;
                    }
                    if (lent == InvariantChecker.readFields(named, reading, Map.of(),
                            InvariantChecker.Reach.EVERYTHING)) {
                        lentItsOwn++;
                    }
                }
            }
        }
        assertTrue(lentPastTheSupposing > 0,
                "no name of the chain has a value under any supposing, so nothing here could tell"
                        + " a reading lent past the supposed name from one that stops there");
        assertTrue(lentItsOwn > 0,
                "no declaration was lent its own reading under any supposing, so nothing here"
                        + " could tell a supposing that reads past a rule from one that stops");
    }

    /**
     * A declaration's own reading is borrowed once for all the supposings of one count that read it
     * as its own.
     *
     * <p>Borrowing it records, against the question borrowing it, everything its making read; a
     * search that borrowed it again for every supposing would record the same reads once per
     * supposing, and a ring's readings read the whole ring.
     */
    @Test
    void aDeclarationsOwnReadingIsBorrowedOnceForEverySupposingOfOneCount() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        compilation.answerEverything();
        RuleReadingSource source = RuleReadings.of(compilation, "demo");
        DeclarationReadings lender = compilation.db().readings();
        int[] borrowed = {0};
        DeclarationReadings counting = new DeclarationReadings() {

            @Override
            public StringMachineAnswers of(TypeKey declaration) {
                return lender.of(declaration);
            }

            @Override
            public KnownExtents extents() {
                return lender.extents();
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
                borrowed[0]++;
                return lender.reading(declaration, origin, policy, read);
            }
        };
        RuleReadingContext reading =
                RuleReadingContext.of(source, ReadAs.THE_COMPILATION_DOES, counting);
        Supposing.Across across = new Supposing.Across(source);
        // Nothing is written under either ring, so neither supposing stops a reading anywhere.
        Supposing.of(Set.of(declared("Q1")), across).readingOf(declared("Holds"), reading);
        Supposing.of(Set.of(declared("R2")), across).readingOf(declared("Holds"), reading);

        assertEquals(1, borrowed[0],
                "a declaration's own reading was borrowed again for a second supposing");
    }

    /**
     * What a count reads off {@code read}: whether its rules leave {@code named} anything, and at
     * the value and each of its fields how many whole numbers stand there and which small sizes
     * a collection there may hold.
     */
    private static List<Object> saidBy(DeclarationReading read, TypeSymbol.AtModule named,
                                       RuleReadingContext reading, InvariantChecker.Reach reach,
                                       RuleReadingSource source) {
        List<Object> said = new ArrayList<>();
        said.add(FieldDomains.of(read, reading, reach)
                .holdsNothing(reading.readings().of(named.key())));
        OccurrenceCounts counts = OccurrenceCounts.of(read.seeded());
        OccurrenceValues values = OccurrenceValues.of(read.seeded());
        List<RuleKey> places = new ArrayList<>(List.of(RuleKey.THE_VALUE));
        source.fieldTypes().of(named).keySet().forEach(field -> places.add(RuleKey.of(field)));
        for (RuleKey place : places) {
            said.add(place + " " + values.wholeValuesAt(place));
            for (long size = 0; size <= 3; size++) {
                said.add(place + " " + size + " " + counts.mayHoldExactly(place, size));
            }
        }
        return said;
    }

    private static TypeSymbol.AtModule declared(String declaration) {
        return TypeSymbols.declared(new TypeKey("demo", declaration));
    }
}
