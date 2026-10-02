package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a count comes to under a supposing does not depend on which readings the supposing shares,
 * nor on whether a reading stops at a supposed name with nothing written under it.
 *
 * <p>A count reads a declaration's rules once and hands that one reading to every question it asks
 * of them: whether they leave anything, how many whole numbers they leave at a place, and which sizes
 * they leave a collection there. And the reading handed over is not always made for the declaration.
 * A newtype that writes nothing, worn over another that writes nothing, is handed the reading of the
 * one beneath, as its own reading is; a supposing hands it the same way down to the first name it
 * stops at; and a supposing that stops nowhere hands each declaration its own reading, borrowed once.
 * Lent past a supposed name, a reading would read the rules the supposing was about.
 *
 * <p>Held two ways, because two different things are being trusted. That sharing changes nothing is
 * held on what the count comes to: every declaration is counted under every supposing once in the
 * compilation's world and once in a world of its own, where nothing is lent and every declaration is
 * read as itself — so whatever a count comes to read off a reading, the comparison reads it too. That
 * a supposing need not stop at a name with no rule under it is a claim about the reading and not
 * about sharing, and is held on the reading: against one stopping at the supposed name, every
 * question a count can ask of it is asked of both.
 *
 * <p>The model writes the shapes those questions can tell apart — a chain of names over a number
 * with three values, a set of them asked to hold two, a rule about a place deep under a record — and
 * each comparison says it saw an answer that a reading which had read the wrong rules would not give.
 */
class AReadingUnderASupposingIsTheOneThatStopsThereTest {

    private static final String MODULE = """
            module demo

            data Empty = Int
                invariant none = value >= 2 && value <= 1

            data X0 = Empty
            data X1 = X0
            data X2 = X1
            data X3 = X2

            data Small = Int
                invariant few = value >= 1 && value <= 3
            data S0 = Small
            data S1 = S0
            data S2 = S1

            data Bag = { xs: Set<S2>, at: S1 }
                invariant two = Set.size(xs) >= 2

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

    private static final List<String> NAMES = List.of("Empty", "X0", "X1", "X2", "X3", "Small",
            "S0", "S1", "S2", "Bag", "R1", "R2", "R3", "Into", "P1", "P2", "P3", "Q1", "Q2",
            "Holds", "Outer");

    /** Every size a count asks a collection about, and one past them. */
    private static final long SIZES = CardinalityTransfer.ENUMERATION_LIMIT + 1L;

    /**
     * Every declaration counted under nothing supposed and under every one name supposed, in both
     * orders, comes to the same in the compilation's world as in a world that lends nothing.
     */
    @Test
    void everyDeclarationCountsTheSameWhateverItsReadingWasSharedWith() {
        Compilation compilation = compiled();
        RuleReadingSource source = RuleReadings.of(compilation, "demo");
        RuleReadingContext shared = RuleReadingContext.of(source, ReadAs.THE_COMPILATION_DOES,
                compilation.db().readings());
        // The same rules, under an origin nobody else has: no lender hands it a reading made for
        // any other declaration, and no name is read as the one beneath it.
        RuleReadingSource itsOwn = new RuleReadingSource(source.symbols(), source.invariants(),
                source.declarations(), source.newtypes(), source.bindings(), source.written());
        RuleReadingContext alone = RuleReadingContext.unshared(itsOwn, ReadAs.THE_COMPILATION_DOES);
        Map<String, Hir.Def> defs = new LinkedHashMap<>();
        compilation.module("demo").defs()
                .forEach(each -> defs.put(each.declaration().node().name(),
                        each.declaration().node()));
        // Nothing known of any name, so whatever a count comes to it read off the rules.
        Map<TypeSymbol, Cardinality> unknown = new LinkedHashMap<>();
        NAMES.forEach(each -> unknown.put(declared(each), Cardinality.UNKNOWN));
        List<String> backwards = new ArrayList<>(NAMES);
        Collections.reverse(backwards);
        List<Set<TypeSymbol>> supposings = new ArrayList<>();
        supposings.add(Set.of());
        NAMES.forEach(each -> supposings.add(Set.of(declared(each))));
        Set<Cardinality> seen = new HashSet<>();
        for (Set<TypeSymbol> supposed : supposings) {
            for (List<String> order : List.of(NAMES, backwards)) {
                Supposing sharing = Supposing.of(supposed, new Supposing.Across(source));
                Supposing notSharing = Supposing.of(supposed, new Supposing.Across(itsOwn));
                for (String asked : order) {
                    TypeSymbol.AtModule named = declared(asked);
                    if (supposed.contains(named)) {
                        continue;
                    }
                    Cardinality lent = CardinalityTransfer.upperOf(named, defs.get(asked),
                            shared, Answers.settled(unknown), sharing);
                    Cardinality own = CardinalityTransfer.upperOf(named, defs.get(asked),
                            alone, Answers.settled(unknown), notSharing);
                    assertEquals(String.valueOf(own), String.valueOf(lent),
                            () -> asked + " under " + supposed + " counts otherwise when its"
                                    + " reading is shared");
                    seen.add(own instanceof Cardinality.None ? null : own);
                }
            }
        }
        // A count of three is the chain over three values read through its rules, and a count of
        // none is a contradiction the rules were read far enough to find.
        assertTrue(seen.contains(Cardinality.atMost(3)) && seen.contains(null)
                        && seen.contains(Cardinality.UNKNOWN),
                () -> "the model no longer comes to a count that a reading of the wrong rules"
                        + " would miss: " + seen);
    }

    /**
     * A reading a supposing hands out says, to every question a count can ask of it, what a reading
     * of the declaration stopping at the supposed name says.
     */
    @Test
    void everyQuestionACountAsksIsAnsweredAsAReadingThatStopsThereAnswersIt() {
        Compilation compilation = compiled();
        RuleReadingSource source = RuleReadings.of(compilation, "demo");
        RuleReadingContext reading = RuleReadingContext.of(source, ReadAs.THE_COMPILATION_DOES,
                compilation.db().readings());
        Supposing.Across across = new Supposing.Across(source);
        List<String> backwards = new ArrayList<>(NAMES);
        Collections.reverse(backwards);
        Set<String> told = new HashSet<>();
        int lentItsOwn = 0;
        for (String supposed : NAMES) {
            InvariantChecker.Reach stopsThere =
                    InvariantChecker.Reach.stoppingAt(Set.of(declared(supposed)));
            for (List<String> order : List.of(NAMES, backwards)) {
                Supposing supposing = Supposing.of(Set.of(declared(supposed)), across);
                for (String asked : order) {
                    if (asked.equals(supposed)) {
                        continue;
                    }
                    TypeSymbol.AtModule named = declared(asked);
                    DeclarationReading lent = supposing.readingOf(named, reading);
                    List<String> own = saidBy(InvariantChecker.readFields(
                            named, reading, Map.of(), stopsThere), named, reading, stopsThere,
                            source);
                    List<String> handed = saidBy(lent, named, reading, supposing.reach(), source);
                    assertEquals(own.size(), handed.size(), "the same questions were asked");
                    for (int each = 0; each < own.size(); each++) {
                        int at = each;
                        assertEquals(own.get(at), handed.get(at), () -> asked + " under "
                                + supposed + " supposed was lent a reading that says something"
                                + " else");
                    }
                    told.addAll(own);
                    if (lent == InvariantChecker.readFields(named, reading, Map.of(),
                            InvariantChecker.Reach.EVERYTHING)) {
                        lentItsOwn++;
                    }
                }
            }
        }
        // Answers a reading of the wrong rules would not give: the chain over three values counted
        // at three, a set of two refused a size of one, a deep rule's contradiction found, and the
        // chain over the empty number left with nothing to contradict once its bottom is supposed.
        for (String expected : List.of("value at most 3", "xs 1 exactly false",
                "holds nothing true", "holds nothing false")) {
            assertTrue(told.contains(expected),
                    () -> "no reading here said `" + expected + "`, so nothing here tells a"
                            + " reading of the wrong rules from the right one");
        }
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
        Compilation compilation = compiled();
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
     * Every answer a count can read off {@code read}, each said with what it was asked: whether the
     * rules leave {@code named} anything, and at the value and each field how many whole numbers
     * stand there and every size a collection there may hold exactly, at least and at most.
     */
    private static List<String> saidBy(DeclarationReading read, TypeSymbol.AtModule named,
                                       RuleReadingContext reading, InvariantChecker.Reach reach,
                                       RuleReadingSource source) {
        List<String> said = new ArrayList<>();
        said.add("holds nothing " + FieldDomains.of(read, reading, reach)
                .holdsNothing(reading.readings().of(named.key())).isPresent());
        OccurrenceCounts counts = OccurrenceCounts.of(read.seeded());
        OccurrenceValues values = OccurrenceValues.of(read.seeded());
        List<RuleKey> places = new ArrayList<>(List.of(RuleKey.THE_VALUE));
        source.fieldTypes().of(named).keySet().forEach(field -> places.add(RuleKey.of(field)));
        for (RuleKey place : places) {
            String at = place.isTheValueItself() ? "value" : place.toString();
            said.add(at + " " + values.wholeValuesAt(place));
            for (long size = 0; size <= SIZES; size++) {
                said.add(at + " " + size + " exactly " + counts.mayHoldExactly(place, size));
                said.add(at + " " + size + " at least " + counts.mayHoldAtLeast(place, size));
                said.add(at + " " + size + " at most " + counts.mayHoldAtMost(place, size));
            }
        }
        return said;
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSources(List.of(MODULE), ModulePath.EMPTY);
        compilation.answerEverything();
        return compilation;
    }

    private static TypeSymbol.AtModule declared(String declaration) {
        return TypeSymbols.declared(new TypeKey("demo", declaration));
    }
}
