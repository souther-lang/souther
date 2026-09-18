package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A condition an account says the search was narrowed by is one the region carries.
 *
 * <p>Three things were one before this. Whether a comparison could be read, whether the region's
 * algebra can carry what was read, and whether the region came out narrower are three answers, and
 * the middle one is what being taken in means. Read off the first, a difference between two
 * positions holding records — read perfectly, and a distance on nothing — went down as a condition
 * the search had been narrowed by while the region it reached was the region it started as. Read
 * off the third, a condition the rules already hold would go down as one nothing could carry.
 *
 * <p>So the region is asked, and it answers about itself rather than being watched for a change.
 */
class AConditionRecordedAsTakenInIsOneTheRegionRepresentsTest {

    private static final String MODEL = """
            module example.noorder

            data K = { id: Int }

            data Pair = { a: String, b: String, m: Int, n: Int }

            behavior recordsAreEqual : (a: K, b: K) -> Bool
            let recordsAreEqual (a, b) = a == b

            behavior textBelowAnotherText : (p: Pair) -> Bool
            let textBelowAnotherText (p) = p.a < p.b

            behavior countBelowAnotherCount : (p: Pair) -> Bool
            let countBelowAnotherCount (p) = p.m < p.n
            """;

    /** The anchor a report would name a hand-written condition by, which nothing here asks about. */
    private static final ConditionReportAnchor WHERE =
            new ConditionReportAnchor.WhereTheReadingMetIt(
                    "m", new ConditionOccurrence("b", 0));

    /**
     * A comparison of two positions standing on no order is declined, and says which shortfall it
     * is.
     *
     * <p>Not the word for a reading that fell short and not the word for a rule that constrains
     * nothing: this rule was read from end to end and constrains both of the positions it names.
     * What is missing is an order to measure them on, which is where an author looks.
     */
    @Test
    void aComparisonOverPositionsWithNoOrderIsDeclined() {
        for (boolean holding : List.of(true, false)) {
            OnTheWay.Declined declined = assertInstanceOf(OnTheWay.Declined.class,
                    only("recordsAreEqual", holding),
                    "a difference between two records is a distance on nothing, so no search was"
                            + " narrowed by it");
            assertEquals(new OnTheWay.Why.QuantityStandsOnNoOrder(), declined.why());
        }
    }

    /**
     * And an order that counts nothing is not that, which is the control the claim above needs.
     *
     * <p>What decides this is whether the positions stand on an order, and never whether that order
     * counts: two strings stand a distance apart on an order with no numbers under it, and the
     * arithmetic carries their difference. A gate written on counting would take these conditions
     * away from a region that represents them perfectly well, which is the same defect facing the
     * other way.
     */
    @Test
    void anOrderThatCountsNothingIsStillAnOrder() {
        for (String behavior : List.of("textBelowAnotherText", "countBelowAnotherCount")) {
            assertInstanceOf(TakenConstraint.Affine.class, taken(behavior),
                    behavior + " is a difference between two positions the region carries");
        }
    }

    /** And the region says the same thing when it is asked directly, which is where the account's
     *  answer comes from. */
    @Test
    void theRegionItselfRefusesAFormOverATermWithNoOrder() {
        SearchRegion.Assumption asked = regionOf("recordsAreEqual")
                .assuming(difference("recordsAreEqual", "a", "b"), Rel.EQ);

        SearchRegion.Refusal.NoOrderUnderATerm why = assertInstanceOf(
                SearchRegion.Refusal.NoOrderUnderATerm.class,
                assertInstanceOf(SearchRegion.Assumption.Refused.class, asked,
                        "the region has no order for either position").why());
        assertEquals(pathOf("recordsAreEqual", "a"), why.term().subjectPath(),
                "and it names the position it has none for");
    }

    /**
     * Taking a constraint in twice takes it in, and leaves the region where it was.
     *
     * <p>The case a reader is most likely to simplify away. A region that says it took a constraint
     * in is not promising to have moved: what it already holds it holds, and nothing was refused.
     * Read as "taken in means the region changed", this second taking would be reported as a
     * condition the search was not narrowed by — which is a decline invented out of a rule the
     * region carries.
     */
    @Test
    void aConstraintAlreadyHeldIsTakenInAndNarrowsNothing() {
        TakenConstraint.Affine affine = assertInstanceOf(TakenConstraint.Affine.class,
                taken("countBelowAnotherCount"));
        SearchRegion once = regionOf("countBelowAnotherCount")
                .assuming(affine.form(), affine.rel()).taken();

        SearchRegion.Assumption again = once.assuming(affine.form(), affine.rel());

        assertInstanceOf(SearchRegion.Assumption.Taken.class, again,
                "a constraint the rules already hold is one the region represents");
        assertSame(once, again.taken(),
                "and holding it again leaves the region exactly where it was");
    }

    /**
     * And a region asked to take in what an account calls taken in never refuses.
     *
     * <p>The other end of the contract, watched where a region would quietly answer instead. A
     * refusal here is two readings of one constraint disagreeing, and the region it would leave is
     * wider than every reader of the account was told the search had been narrowed to — so it stops
     * the compilation rather than reaching a search as a region.
     */
    @Test
    void aTakenInEntryTheRegionCannotCarryIsRefusedLoudly() {
        WayToTheBorder forged = new WayToTheBorder(List.of(new OnTheWay.TakenIn(WHERE,
                new TakenConstraint.Affine(
                        difference("recordsAreEqual", "a", "b"), Rel.EQ))));

        assertThrows(IllegalStateException.class,
                () -> forged.narrowing(regionOf("recordsAreEqual")),
                "a constraint recorded as taken in and refused by the region is this compiler"
                        + " holding two readings of it");
    }

    /**
     * {@code one - other} over two of the behavior's positions.
     *
     * <p>The positions are taken from the reading rather than spelled here, so the form is over the
     * places this reading has, and a term of it is a term the region can be asked about. What is
     * assembled is the arithmetic, which is what these two tests are about — the reading has none
     * to hand for the record pair, since the walk now declines the comparison it would come from.
     */
    private static LinearForm<NumericTerm> difference(String behavior, String one, String other) {
        Map<NumericTerm, BigDecimal> coefs = new LinkedHashMap<>();
        coefs.put(new NumericTerm.ValueOf(pathOf(behavior, one)), BigDecimal.ONE);
        coefs.put(new NumericTerm.ValueOf(pathOf(behavior, other)), BigDecimal.ONE.negate());
        return new LinearForm<>(BigDecimal.ZERO, coefs);
    }

    /** Where the reading of the behavior's input has the position spelled {@code spelled}. */
    private static TermPath pathOf(String behavior, String spelled) {
        List<TermPath> positions = readingOf(behavior).read().domain().positions().stream()
                .map(souther.compiler.inputs.Position::path).toList();
        return positions.stream().filter(each -> each.toString().equals(spelled)).findFirst()
                .orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + positions));
    }

    /** The constraint the body's single condition landed in, coming out the way it was written. */
    private static TakenConstraint taken(String behavior) {
        return assertInstanceOf(OnTheWay.TakenIn.class, only(behavior, true),
                behavior + " states something a search can compose against").taken();
    }

    /** The one thing the body's single condition states. */
    private static OnTheWay only(String behavior, boolean holding) {
        List<OnTheWay> stated = stating(behavior, holding);
        assertEquals(1, stated.size(), () -> behavior + " is one condition: " + stated);
        return stated.get(0);
    }

    private static List<OnTheWay> stating(String behavior, boolean holding) {
        return readingOf(behavior).stating(holding);
    }

    /** The region this compiler builds for the behavior's input, off the reading its conditions
     *  were read against — so a term of one is a term of the other. */
    private static SearchRegion regionOf(String behavior) {
        return readingOf(behavior).read().quantities().region();
    }

    /** One behavior of the model, read once — the reading the conditions are read against and the
     *  region is built from, so that a term of the one is a term of the other. */
    private record Read(Core body, souther.compiler.inputs.InputReading read, InputReads reads,
                        RuleReadingSource rules, String module, String behavior) {

        List<OnTheWay> stating(boolean holding) {
            return ReachingCuts.stating(Condition.of(body, reads, rules.symbols(),
                    rules.newtypes(), new ConditionNumbering(module, behavior)), read, holding);
        }
    }

    private static final Map<String, Read> READINGS = new java.util.concurrent.ConcurrentHashMap<>();

    private static Read readingOf(String behavior) {
        return READINGS.computeIfAbsent(behavior, name -> {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.answerEverything();
            String module = compilation.modules().get(0);
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            assertNotNull(checked, "the model under test compiles");
            Core body = checked.behaviorBodies().get(name);
            assertNotNull(body, () -> "the model under test writes " + name);
            RuleReadingSource rules = RuleReadings.of(compilation, module);
            souther.compiler.inputs.InputDomain inputs =
                    compilation.db().ask(new Adequacy.Inputs(module)).value().get(name);
            InputReads reads = InputReads.ofParameters(inputs.parameterReads(),
                    checked.elementBindings().get(name));
            return new Read(body, inputs.reading(rules), reads, rules, module, name);
        });
    }
}
