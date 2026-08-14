package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Sig;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.TypeName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The equivalence classes a model already states.
 *
 * <p>What is being checked as much as anything is the restraint: a position the model draws no line
 * through gets no classes. Splitting an unbounded {@code Int} at zero would measure a rule nobody
 * wrote and then report a gap for not having tested it.
 */
class PartitionsTest {

    private static Partitions.Partitioning partitioningOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Hir.Module prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        assertNotNull(prepared);
        assertNotNull(sigs);
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals(behavior)).findFirst().orElseThrow();
        return Partitions.of(spec, sigs.get(behavior),
                compilation.db().ask(new Shapes.Scope(module)).value(), Exclusions.NONE);
    }

    private static Axis axis(Partitions.Partitioning partitioning, String path) {
        return partitioning.axes().stream().filter(a -> a.path().toString().equals(path))
                .findFirst().orElseThrow(() -> new AssertionError("no axis at " + path
                        + "; had " + partitioning.axes().stream().map(a -> a.path().toString())
                        .toList()));
    }

    private static List<String> classIds(Axis axis) {
        return axis.classes().stream().map(PartitionClass::id).toList();
    }

    private static final String KINDS = """
            module example.trip

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Note = String

            data Request = { kind: Kind, cost: Amount, urgent: Bool, memo: Note?, note: Note }

            data Accepted = { at: String }

            behavior submit : (request: Request) -> Accepted
                constructs Accepted

            let submit (request) = Accepted { at = "now" }
            """;

    @Test
    void aSumsCasesAreItsClasses() {
        Axis kind = axis(partitioningOf(KINDS, "submit"), "request.kind");

        assertEquals(List.of("Domestic", "Overseas"), classIds(kind));
        assertTrue(kind.classes().stream().allMatch(PartitionClass::generatable),
                "a unit case is written as its own name");
    }

    @Test
    void aBoolIsTwoClassesAndAnOptionalIsTwo() {
        Partitions.Partitioning partitioning = partitioningOf(KINDS, "submit");

        assertEquals(List.of("true", "false"), classIds(axis(partitioning, "request.urgent")));
        assertEquals(List.of("None", "Some"), classIds(axis(partitioning, "request.memo")));
    }

    /** The restraint. A bound refuses everything outside it at construction, so there is no class on
     * the far side to cover — only an edge worth a row. */
    @Test
    void aBoundedNewtypeHasBoundariesAndNoClasses() {
        Axis cost = axis(partitioningOf(KINDS, "submit"), "request.cost");

        assertEquals(List.of(), classIds(cost));
        assertFalse(cost.derivable());
        assertTrue(cost.measurable(), "there is still an edge to reach");
        assertEquals(List.of(new ObservedValue.Integer(0L), new ObservedValue.Integer(1000L)),
                cost.cuts().stream().map(Cut::value).toList());
    }

    /**
     * A rule reaches through as many names as are wrapped round the number.
     *
     * <p>`data StartMinute = Minute` is one the language compares and bounds, and was one the
     * derivation read nothing off — the range reader stopped at the first name and the position came
     * back as one the model draws no line through (#461). Both ends and the rule between them are
     * read at the numbers underneath, so the cuts are the type's edges taken in by the record.
     */
    @Test
    void aBoundReachesThroughEveryNameWrappedRoundTheNumber() {
        Partitions.Partitioning span = partitioningOf("""
                module example.nested

                data Minute = Int
                    invariant withinDay = value >= 0 && value <= 1440

                data StartMinute = Minute
                data EndMinute = Minute

                data Span =
                    { from: StartMinute
                    , to: EndMinute
                    }
                    invariant ordered = from.value < to.value

                data Ok = { at: String }

                behavior classify : (span: Span) -> Ok
                    constructs Ok

                let classify (span) = Ok { at = "x" }
                """, "classify");

        assertEquals(List.of(new ObservedValue.Integer(0L), new ObservedValue.Integer(1439L)),
                axis(span, "span.from").cuts().stream().map(Cut::value).toList());
        assertEquals(List.of(new ObservedValue.Integer(1L), new ObservedValue.Integer(1440L)),
                axis(span, "span.to").cuts().stream().map(Cut::value).toList());
        assertEquals(List.of("invariant Minute (min)", "invariant Minute (max) within Span"),
                axis(span, "span.from").cuts().stream()
                        .map(c -> c.origins().get(0).describe()).toList(),
                "the rule that drew each end is the one that wrote it, not the outermost name");
    }

    /**
     * Bounds on two of the names a value wears intersect, and each end is owed to the rule that put
     * it there.
     *
     * <p>Neither layer alone says the range is `[0, 10]`. A reader that took the outermost
     * declaration's clauses would answer `[nothing, 10]`, and one that kept a single name per end
     * would drop an obligation where two layers state the same bound.
     */
    @Test
    void boundsOnTwoOfTheNamesIntersectAndBothAreOwed() {
        Partitions.Partitioning wrapped = partitioningOf("""
                module example.wrapped

                data Inner = Int
                    invariant innerMin = value >= 0

                data Outer = Inner
                    invariant outerMin = value >= 0
                    invariant outerMax = value <= 10

                data Ok = { at: String }

                behavior classify : (o: Outer) -> Ok
                    constructs Ok

                let classify (o) = Ok { at = "x" }
                """, "classify");
        Axis o = axis(wrapped, "o");

        assertEquals(List.of(new ObservedValue.Integer(0L), new ObservedValue.Integer(10L)),
                o.cuts().stream().map(Cut::value).toList());
        assertEquals(List.of("invariant Outer (min)", "invariant Inner (min)"),
                o.cuts().get(0).origins().stream().map(OriginRef::describe).toList(),
                "one value, two rules, and a row is owed to each");
        assertEquals(List.of("invariant Outer (max)"),
                o.cuts().get(1).origins().stream().map(OriginRef::describe).toList());
    }

    /** A `Decimal` under two names reads the same way. */
    @Test
    void theSameHoldsOverADecimalBase() {
        Partitions.Partitioning share = partitioningOf("""
                module example.share

                data Ratio = Decimal
                    invariant withinOne = value >= 0.0m && value <= 1.0m

                data Share = Ratio

                data Ok = { at: String }

                behavior classify : (s: Share) -> Ok
                    constructs Ok

                let classify (s) = Ok { at = "x" }
                """, "classify");

        assertEquals(List.of(new ObservedValue.Decimal(java.math.BigDecimal.ZERO),
                        new ObservedValue.Decimal(java.math.BigDecimal.ONE)),
                axis(share, "s").cuts().stream().map(Cut::value).toList(),
                "how many places a literal was written to is not where the line is");
    }

    @Test
    void aTypeTheModelDrawsNoLineThroughIsNotDerivable() {
        Axis note = axis(partitioningOf(KINDS, "submit"), "request.note");

        assertFalse(note.measurable());
        assertEquals(List.of(), classIds(note));
    }

    @Test
    void aCutRemembersTheRuleThatDrewIt() {
        Axis cost = axis(partitioningOf(KINDS, "submit"), "request.cost");

        OriginRef origin = cost.cuts().get(0).origins().get(0);
        OriginRef.InvariantOrigin invariant =
                org.junit.jupiter.api.Assertions.assertInstanceOf(OriginRef.InvariantOrigin.class,
                        origin);
        assertEquals("Amount", invariant.type().name());
    }

    /** A record is taken apart, and only so far: two levels reach a field of a record a parameter
     * holds, which is where rules are written. */
    @Test
    void aProductIsTakenApartFieldByField() {
        List<String> paths = partitioningOf(KINDS, "submit").axes().stream()
                .map(a -> a.path().toString()).toList();

        assertEquals(List.of("request.kind", "request.cost", "request.urgent", "request.memo",
                "request.note"), paths);
    }

    @Test
    void classifiersRecogniseTheValuesRowsCarry() {
        Partitions.Partitioning partitioning = partitioningOf(KINDS, "submit");
        Axis kind = axis(partitioning, "request.kind");
        assertEquals(Membership.MATCH, kind.classes().get(0).classifier().membershipOf(
                        new ObservedValue.Unit(TypeSymbols.declared(new TypeKey("example.trip", "Domestic")))),
                "a unit case is recognised by the type it names");

        Axis urgent = axis(partitioning, "request.urgent");
        assertEquals(Membership.MATCH,
                urgent.classOf("true").classifier().membershipOf(new ObservedValue.Bool(true)));
        assertEquals(Membership.NO_MATCH,
                urgent.classOf("true").classifier().membershipOf(new ObservedValue.Bool(false)));

        Axis memo = axis(partitioning, "request.memo");
        assertEquals(Membership.MATCH,
                memo.classOf("None").classifier().membershipOf(new ObservedValue.Absent()));
        assertEquals(Membership.NO_MATCH,
                memo.classOf("None").classifier().membershipOf(new ObservedValue.Text("x")));
    }

    /**
     * The shipping-fee example from smdd-book chapter 8: two bands the model names, so two axes of two
     * classes each. The 2999/3000 boundary the book also derives comes from the threshold the rule
     * compares against, which is read from the behavior's body rather than from these types.
     */
    @Test
    void theBandsAModelNamesAreItsClasses() {
        Partitions.Partitioning shipping = partitioningOf("""
                module example.shipping

                data UnderThreeThousand
                data ThreeThousandOrOver
                data AmountBand = UnderThreeThousand | ThreeThousandOrOver

                data Remote
                data NotRemote
                data RegionBand = Remote | NotRemote

                data Fee = { yen: Int }

                behavior feeFor : (amount: AmountBand, region: RegionBand) -> Fee
                    constructs Fee

                let feeFor (amount, region) = Fee { yen = 0 }
                """, "feeFor");

        assertEquals(2, shipping.derivable().size());
        assertEquals(List.of("UnderThreeThousand", "ThreeThousandOrOver"),
                classIds(axis(shipping, "amount")));
        assertEquals(List.of("Remote", "NotRemote"), classIds(axis(shipping, "region")));
    }

    @Test
    void pastTheAxisLimitTheRestAreDroppedAndNamedRatherThanMerged() {
        StringBuilder fields = new StringBuilder();
        for (int i = 0; i < 15; i++) {
            fields.append("f").append(i).append(": Bool, ");
        }
        String wide = """
                module example.wide

                data Wide = { %s }
                data Done = { at: String }

                behavior run : (wide: Wide) -> Done
                    constructs Done

                let run (wide) = Done { at = "now" }
                """.formatted(fields.substring(0, fields.length() - 2));

        Partitions.Partitioning partitioning = partitioningOf(wide, "run");

        assertEquals(Partitions.MAX_AXES, partitioning.derivable().size());
        assertEquals(3, partitioning.omitted().size());
        assertTrue(partitioning.omitted().get(0).axis().toString().contains("run/wide.f12"),
                partitioning.omitted().get(0).axis().toString());
        // A `Bool` is classified and never cut, so dropping one loses a measure nothing refuses a
        // build over. What a dropped axis was carrying is decided here because it cannot be read back:
        // a position nobody measured leaves the same absence as one the rows cover.
        assertTrue(partitioning.omitted().stream()
                .noneMatch(Partitions.OmittedAxis::carriedAnObligation));
    }
}
