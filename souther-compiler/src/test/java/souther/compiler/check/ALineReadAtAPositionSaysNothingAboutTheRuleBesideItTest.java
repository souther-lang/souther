package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.inputs.BlockReason;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule saying where a position's values stop that no end came out of, named at every position it
 * is about.
 *
 * <p>The invariant's half of what a {@code guard}'s comparison already answers (ADR-0090). Both
 * draw lines, both can be written in a form this compiler does not read, and a reader is told the
 * same thing about either — so an invariant's clause that placed no end has to be said, and said
 * once.
 *
 * <p>What made it silent was that a position carries more than one statement. The account was kept
 * as what the position was left with if nothing divided it, so a bound on a field's own type
 * answered for the record's clause about that same field and the clause was dropped without a word:
 * two declarations differing by one {@code invariant value >= 0} said opposite things about the
 * clause above them. That is what the pair below is for — the same relation, once where the fields'
 * types draw a line and once where they do not — and it is the pair, not either half, that holds
 * the fix.
 */
class ALineReadAtAPositionSaysNothingAboutTheRuleBesideItTest {

    private static FieldDomains readingOf(String source, String type) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols, "the model under test compiles");
        TypeSymbol named = TypeSymbols.declared(new TypeKey(module, type));
        Hir.Data data = (Hir.Data) symbols.declarations().declaration(named.key());
        assertNotNull(data, "no `" + type + "` declared");
        return FieldDomains.of(named, data, symbols);
    }

    private static final String MEASURED = """
            module example.parcels

            data Cm = Int
                invariant value >= 0

            data Parcel = { length: Cm, width: Cm }
                invariant Int.add(length.value, width.value) <= 150
            """;

    private static final String BARE = """
            module example.parcels

            data Parcel = { length: Int, width: Int }
                invariant Int.add(length, width) <= 150
            """;

    /**
     * A clause comparing an arithmetic form over two fields, where nothing else divides them.
     *
     * <p>The half that always worked, here so that the half below cannot pass by accident: what
     * separates the two is one {@code invariant value >= 0} on the fields' own type, which is not a
     * fact about this clause.
     */
    @Test
    void aClauseNoEndCameOutOfIsNamedAtEveryFieldItCompares() {
        FieldDomains read = readingOf(BARE, "Parcel");

        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "length"));
        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "width"));
    }

    /**
     * And says so where the fields' own type has already drawn a line through them.
     *
     * <p>Issue #868. {@code Cm}'s own bound places an end at each field, and the record's clause
     * about the pair is a second statement about the same positions — so the report owed both, and
     * said only the first while the {@code guard} of the same shape two declarations away named
     * both of the positions it compared.
     */
    @Test
    void andSaysSoWhereTheFieldsOwnTypeAlreadyDrewALine() {
        FieldDomains read = readingOf(MEASURED, "Parcel");

        assertFalse(read.placedAt("length").isEmpty(), "`Cm` places an end here");
        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "length"));
        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "width"));
    }

    /**
     * A rule an end did come out of is named no way.
     *
     * <p>The reading that draws lines is what answers, and it read this one: a report naming it
     * would send an author after a boundary it is about to print two lines below.
     */
    @Test
    void anEndThisReadIsNotNamed() {
        FieldDomains read = readingOf("""
                module example.parcels

                data Cm = Int
                    invariant value >= 0

                data Parcel = { length: Cm, width: Cm }
                    invariant length.value <= 150
                """, "Parcel");

        assertFalse(read.placedAt("length").isEmpty());
        assertEquals(List.of(), read.unreadAt("length"));
        assertEquals(List.of(), read.unreadAt("width"));
    }

    /**
     * A rule of another shape is not one of these either.
     *
     * <p>A format, a membership, a denial: each says which values exist rather than where they
     * stop, and a report has nowhere to put one as a line. Named here, an author would be sent
     * after a boundary nobody wrote.
     */
    @Test
    void aRuleThatIsNotAboutWhereTheValuesStopIsNotNamedAsALine() {
        FieldDomains read = readingOf("""
                module example.parcels

                data Parcel = { label: String, length: Int }
                    invariant String.matches(label, "[A-Z]+")
                    invariant length /= 5
                """, "Parcel");

        assertEquals(List.of(), read.unreadAt("label"));
        assertEquals(List.of(), read.unreadAt("length"));
    }

    /**
     * An equality least of all, though it reaches this reading as a comparison that placed no end.
     *
     * <p>It names a value rather than an end, and the reading of values holds it. Read off "no end
     * came out of it", every {@code == 5} in every model would be a line somebody was told to go
     * looking for — which is the failure this whole account is the other side of.
     */
    @Test
    void anEqualityIsNotNamedThoughNoEndCameOutOfIt() {
        FieldDomains read = readingOf("""
                module example.parcels

                data Parcel = { length: Int }
                    invariant length == 5
                """, "Parcel");

        assertEquals(List.of(), read.unreadAt("length"));
    }

    /**
     * A clause relating two fields says that it relates them, at both.
     *
     * <p>Which is a different thing for a reader to do about it: nothing is missing from the
     * carrier — a line drawn on either field against a number would be read — and what a partition
     * of one position is not is a class about two.
     */
    @Test
    void aClauseRelatingTwoFieldsSaysThatItRelatesThem() {
        FieldDomains read = readingOf("""
                module example.spans

                data Bound = Int
                    invariant value >= 0

                data Span = { low: Bound, high: Bound }
                    invariant low < high
                """, "Span");

        assertEquals(List.of(new BlockReason.ComparisonBetweenPositions()), reasonsAt(read, "low"));
        assertEquals(List.of(new BlockReason.ComparisonBetweenPositions()), reasonsAt(read, "high"));
    }

    /**
     * And a clause naming one coordinate on each side is one of those, however the sides are
     * written.
     *
     * <p>The form between the two above: {@code x} against {@code y + 1} is a rule about the pair
     * exactly as {@code x < y} is, and the arithmetic is on the far side of the relation rather
     * than in place of it. Read off whether a side <em>is</em> a coordinate, {@code y + 1} named
     * nothing and this came back as a form nobody could read — which is not what a {@code guard}
     * writing the same comparison is told.
     */
    @Test
    void andSoDoesOneWhereTheSecondPositionIsInsideAnExpression() {
        FieldDomains read = readingOf("""
                module example.spans

                data Pair = { x: Int, y: Int }
                    invariant x < y + 1
                """, "Pair");

        assertEquals(List.of(new BlockReason.ComparisonBetweenPositions()), reasonsAt(read, "x"));
        assertEquals(List.of(new BlockReason.ComparisonBetweenPositions()), reasonsAt(read, "y"));
    }

    /**
     * But one position on both sides of a comparison is not two positions.
     *
     * <p>{@code x < x + 1} names {@code x} either side of it and there is no other position for a
     * class to be about. Told that the rule relates it to another position, a reader goes looking
     * for one the model never wrote; what would let this be read is a reading of the form, which
     * is what the position on the right is inside of.
     */
    @Test
    void butOnePositionOnBothSidesIsNotTwoPositions() {
        FieldDomains read = readingOf("""
                module example.spans

                data Sole = { x: Int }
                    invariant x < x + 1
                """, "Sole");

        assertEquals(List.of(new BlockReason.UnreadComparisonForm()), reasonsAt(read, "x"));
    }

    /**
     * A position whose values carry no order to draw a line on says that, and says it once.
     *
     * <p>A field declared as one case of an enumeration is ordered — the comparison is on the sum's
     * order and typechecks — and the sum's places are not its own, so no line divides it. The
     * carrier, asked of the carrier, exactly as a {@code guard} comparing the same field is
     * answered.
     *
     * <p>The clause reaches the reading of ends all the same, which is what lets it be answered
     * for: a coordinate is a coordinate whether or not a line can be drawn on it. So the second
     * assertion is the one that matters — reading an end here would put a line through a position
     * that has no order to draw one on.
     */
    @Test
    void aPositionNoLineCanBeDrawnOnSaysThatAndIsGivenNoEnd() {
        FieldDomains read = readingOf("""
                module example.stages

                data Prospecting
                data Qualified
                data Won
                data Stage = Prospecting | Qualified | Won

                data Holder = { stage: Qualified }
                    invariant stage >= Prospecting
                """, "Holder");

        assertEquals(List.of(new BlockReason.UnreadComparisonDomain()), reasonsAt(read, "stage"));
        assertEquals(List.of(), read.placedAt("stage"), "no line is drawn where no order is");
    }

    /** And a newtype's own clause reaches the same account, at the position a name wraps. */
    @Test
    void aNewtypesOwnClauseIsNamedAtTheValueItWraps() {
        FieldDomains read = readingOf("""
                module example.stepped

                data Stepped = Int
                    invariant value >= 1 + 1
                """, "Stepped");

        List<FieldDomains.Unread> said = read.unreadAt(FieldDomains.THE_VALUE);
        assertEquals(1, said.size(), () -> "said " + said);
        assertInstanceOf(BlockReason.UnreadComparisonForm.class, said.getFirst().why());
        assertTrue(said.getFirst().from().clause().id().declaredOn().name().endsWith("Stepped"),
                "the rule a reader is sent to look at is the one that wrote the clause");
    }

    private static List<BlockReason> reasonsAt(FieldDomains read, String path) {
        return read.unreadAt(path).stream().map(FieldDomains.Unread::why).toList();
    }
}
