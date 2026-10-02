package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.query.Machines;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.KnownExtents;
import souther.compiler.values.StringFacts;
import souther.compiler.values.StringMachineAnswers;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A newtype that writes nothing, worn over another newtype that writes nothing, is read as the name
 * beneath it.
 *
 * <p>Its value is the same location as the value beneath, no rule of its own is read there, and the
 * walk goes on into the same names — so the reading of the name beneath is its reading, and a chain
 * of such names is read once rather than once per name with the whole chain under each.
 *
 * <p>Only that edge. The first name over a declaration that writes rules reads them as a walk reaches
 * them, and the declaration reads them as its own clauses, so those two are read apart.
 *
 * <p>Held by counting readings and by what the readings answer, not by timing a compile: a chain that
 * is read once per name with the chain under each costs the square of its length, and a measurement
 * of that would pass on a fast machine.
 */
class ANameThatWritesNothingIsReadAsTheNameBeneathItTest {

    /** A record with rules on and between its fields, and three names over it writing nothing. */
    private static final String RANGED = """
            module ranged

            data Span = { lo: Int, hi: Int }
                invariant lo >= 0 && hi <= 9 && lo <= hi
            data Once = Span
            data Twice = Once
            data Thrice = Twice
            """;

    /** {@code length} names, the first of them writing a rule and none of the others writing any. */
    private static String chain(int length) {
        StringBuilder source = new StringBuilder("""
                module chain

                data T1 = Int
                    invariant value >= 1 && value <= 9
                """);
        for (int i = 2; i <= length; i++) {
            source.append("data T").append(i).append(" = T").append(i - 1).append('\n');
        }
        return source.toString();
    }

    @Test
    void aLongerChainOfNamesThatWriteNothingIsReadNoMoreTimes() {
        long few = readingsMadeCompiling(chain(4));
        long many = readingsMadeCompiling(chain(40));

        assertTrue(few > 0, "a chain of four names made no reading, so this measures nothing");
        assertEquals(few, many,
                () -> "a chain of forty names was read " + many + " times against " + few
                        + " for four, so a name that writes nothing over another is read again"
                        + " rather than lent the reading beneath it");
    }

    @Test
    void eachNameIsReadAsTheLowestOfTheNamesThatWriteNothingUnderIt() {
        Compilation compilation = compiled(List.of("""
                module worn

                data T1 = Int
                    invariant value >= 1 && value <= 9
                data T2 = T1
                data T3 = T2
                data T4 = T3

                data Span = { lo: Int, hi: Int }
                    invariant lo <= hi
                data Once = Span
                data Twice = Once
                """));

        assertEquals("T1", ownerOf(compilation, "worn", "T1"),
                "a name writing a rule is read as itself");
        assertEquals("T2", ownerOf(compilation, "worn", "T2"),
                "the first name over one writing a rule reads that rule as a walk reaches it");
        assertEquals("T2", ownerOf(compilation, "worn", "T3"),
                "a name writing nothing over one writing nothing is read as that one");
        assertEquals("T2", ownerOf(compilation, "worn", "T4"),
                "and so is every name above it");
        assertEquals("Once", ownerOf(compilation, "worn", "Once"),
                "a name over a record is read as itself, the record not being a name worn over");
        assertEquals("Once", ownerOf(compilation, "worn", "Twice"),
                "and a name over that one is read as it");
        assertEquals("Span", ownerOf(compilation, "worn", "Span"),
                "a declaration that is no newtype is read as itself");
    }

    @Test
    void aNameOfAnotherModuleIsReadAsTheNameBeneathItThere() {
        Compilation compilation = compiled(List.of("""
                module below exposing ( T1, T2, T3 )

                data T1 = Int
                    invariant value >= 1 && value <= 9
                data T2 = T1
                data T3 = T2
                """, """
                module above

                import below ( T3 )

                data U1 = T3
                data U2 = U1
                """));

        assertEquals("below.T2", qualifiedOwnerOf(compilation, "above", "U1"),
                "a chain that leaves the module is read as the owner the other module answers");
        assertEquals("below.T2", qualifiedOwnerOf(compilation, "above", "U2"),
                "and every name above it is read the same");
    }

    /**
     * A name on a ring, and one on the way to it, is read as itself.
     *
     * <p>With the name on the way written before the ring and after it, because a module's names
     * are walked in the order they are written and the answer is not allowed to depend on that.
     */
    @Test
    void aRingOfNamesLeavesEveryNameOnTheWayItsOwnReading() {
        for (String source : List.of("""
                module ring

                data A = B
                data B = A
                data C = A
                """, """
                module ring

                data C = A
                data A = B
                data B = A
                """)) {
            Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
            compilation.answerEverything();

            for (String each : List.of("A", "B", "C")) {
                assertEquals(each, ownerOf(compilation, "ring", each),
                        "nothing on a ring is beneath the others, so `" + each + "` is read as"
                                + " itself in\n" + source);
            }
        }
    }

    /**
     * A name read as the one beneath it has that one's machines.
     *
     * <p>The machines are what the reading builds, and the reading is one reading of both names. A
     * name that made its answer by reading again would read the owner's rules into a recorder no
     * reading writes to, and come back with nothing.
     */
    @Test
    void aNameReadAsTheOneBeneathHasItsMachines() {
        Compilation compilation = compiled(List.of("""
                module coded

                data S1 = String
                    invariant String.matches("[A-Z]{2}[0-9]{3}", value)
                data S2 = S1
                data S3 = S2
                """));
        assertEquals("S2", ownerOf(compilation, "coded", "S3"),
                "the model under test has a name read as the one beneath it");

        StringFacts owners = machinesOf(compilation, "coded", "S2");
        assertNotEquals(StringFacts.NONE, owners,
                "the owner's reading built machines, so there is something to be handed");
        assertEquals(owners, machinesOf(compilation, "coded", "S3"),
                "the name above has the machines the one reading built");
    }

    /**
     * What the lent reading answers is what the name's own reading answers.
     *
     * <p>Read once through the compilation, where the reading is lent, and once with nothing to
     * borrow, where the name reads its own rules all the way down. The two readings bind their terms
     * under different names, so what is compared is what they come to.
     */
    @Test
    void theReadingLentAnswersWhatTheNamesOwnReadingAnswers() {
        Compilation compilation = compiled(List.of(RANGED));
        assertEquals("Once", ownerOf(compilation, "ranged", "Thrice"),
                "the model under test has a name read as one beneath it");
        RuleReadingSource rules = RuleReadings.of(compilation, "ranged");
        ReadingPolicy policy = compilation.db().ask(new Front.Reading()).value();
        TypeKey thrice = new TypeKey("ranged", "Thrice");

        FieldDomains lent = FieldDomains.of(TypeSymbols.declared(thrice),
                RuleReadingContext.of(rules, policy, compilation.db().readings()));
        FieldDomains own = FieldDomains.of(TypeSymbols.declared(thrice),
                RuleReadingContext.unshared(rules, policy));

        assertEquals("Once", lent.named().key().name(), "the lent reading is the owner's");
        assertEquals("Thrice", own.named().key().name(), "the other is the name's own");
        for (String field : List.of("lo", "hi")) {
            NumberAt.OfWhatNumber value = new NumberAt.OfWhatNumber.OfItsOwnValue();
            assertEquals(own.leftAt(RuleKey.of(field), value), lent.leftAt(RuleKey.of(field), value),
                    "what the rules leave `" + field + "` is the same either way");
        }
        assertEquals(own.placed(), lent.placed(), "and so are the ends the rules place");
        assertEquals(own.withoutAnEnd().size(), lent.withoutAnEnd().size(),
                "and the rules that place none");
        assertTrue(lent.anythingWasWritten(), "the readings compared read the rules at all");
    }

    /**
     * What is derived from a lent reading is derived under the name it is a reading of, whichever
     * name asks first.
     *
     * <p>Asked of a lender directly, with the name above asking first. Through a compilation the
     * owner's machines are asked for before any name is lent its reading, and making them derives
     * under the owner — so a compile cannot tell which name a derivation would have been made under
     * had another name asked first.
     */
    @Test
    void whatALentReadingDerivesIsDerivedUnderItsOwnerWhoeverAsksFirst() {
        Compilation compilation = compiled(List.of(RANGED));
        RuleReadingSource rules = RuleReadings.of(compilation, "ranged");
        ReadingPolicy policy = compilation.db().ask(new Front.Reading()).value();
        TypeSymbol.AtModule once = TypeSymbols.declared(new TypeKey("ranged", "Once"));
        TypeSymbol.AtModule thrice = TypeSymbols.declared(new TypeKey("ranged", "Thrice"));
        LentReadings lender = new LentReadings(new DeclarationReadings() {

            @Override
            public StringMachineAnswers of(TypeKey declaration) {
                return StringMachineAnswers.unborrowed(KnownExtents.NONE);
            }

            @Override
            public TypeSymbol.AtModule ownerOf(TypeSymbol.AtModule declaration) {
                return declaration.equals(thrice) ? once : declaration;
            }
        }, () -> 1, StoreWork.UNWATCHED);
        RuleReadingContext reading = RuleReadingContext.of(rules, policy, lender);

        FieldDomains asked = FieldDomains.of(thrice, reading);

        assertEquals(once, asked.named(),
                "the name above asked first, and what was derived is the owner's reading of itself");
        assertSame(asked, FieldDomains.of(once, reading),
                "and the owner asking afterwards is handed what was derived");
    }

    private static Compilation compiled(List<String> sources) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model under test is a program that can be written");
        return compilation;
    }

    private static long readingsMadeCompiling(String source) {
        long before = InvariantChecker.readingsMade();
        compiled(List.of(source));
        return InvariantChecker.readingsMade() - before;
    }

    /** The name {@code name} of {@code module} is read as, which is of the same module. */
    private static String ownerOf(Compilation compilation, String module, String name) {
        TypeKey owner = qualifiedOwner(compilation, module, name);
        assertEquals(module, owner.module(), "the owner of `" + name + "` is of its module");
        return owner.name();
    }

    private static String qualifiedOwnerOf(Compilation compilation, String module, String name) {
        TypeKey owner = qualifiedOwner(compilation, module, name);
        return owner.module() + "." + owner.name();
    }

    /** The name {@code name} is read as: the one the store answers, or itself where it answers
     *  none. */
    private static TypeKey qualifiedOwner(Compilation compilation, String module, String name) {
        TypeKey named = new TypeKey(module, name);
        Answer<Shapes.ReadAs> owner = compilation.db().ask(new Shapes.ReadingOwnerOf(named));
        return owner.present()
                && owner.value() instanceof Shapes.ReadAs.TheNameBeneath(TypeSymbol.AtModule beneath)
                ? beneath.key() : named;
    }

    private static StringFacts machinesOf(Compilation compilation, String module, String name) {
        Answer<StringFacts> facts =
                compilation.db().ask(new Machines.OfDeclaration(new TypeKey(module, name)));
        assertTrue(facts.present(), "`" + name + "` has machines");
        return facts.value();
    }
}
