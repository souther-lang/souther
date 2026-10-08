package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.DecisionReading;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm selecting a case the declaration already leaves a value narrows nothing, and one selecting
 * a case it leaves none of is one no row takes.
 *
 * <p>The case an arm selects is relative to the type the scrutinee stands as, and a value handed to
 * a parameter of a wider type stands as more than it is. A field declared {@code DecimalPart}
 * matched as a {@code Coefficient} is already the case the arm selects: the location is the one the
 * declaration names, and spelled with the narrowing it is a location the reading of the input holds
 * nothing under. Where the declaration does leave the value several cases, the arm narrows it as
 * it always did.
 */
class AnArmOnACaseTheDeclarationAlreadyMakesNarrowsNothingTest {

    private static final String WIDENED = """
            module repro.nested_refinement

            data WholeDigits = String
                invariant decimalInteger = String.matches("0|[1-9][0-9]{0,71}", value)
            data FractionDigits = String
                invariant decimalFraction = String.matches("[0-9]{0,24}", value)
            data DecimalPart = { whole: WholeDigits, fraction: FractionDigits }
            data Coefficient = WholeDigits | DecimalPart

            data Fraction = { coefficient: DecimalPart }
            data Empty
            data Number = Fraction | Empty

            let coefficientText (c: Coefficient): String =
                match c with
                    | WholeDigits(w) -> w
                    | DecimalPart as d -> d.whole.value ++ "." ++ d.fraction.value

            behavior render : (n: Number) -> String
            let render (n) =
                match n with
                    | Fraction as f -> coefficientText(f.coefficient)
                    | Empty -> ""
            """;

    private static final String NAMED = """
            module probe.arms

            data WholeDigits = String
                invariant decimalInteger = String.matches("0|[1-9][0-9]{0,71}", value)
            data FractionDigits = String
                invariant decimalFraction = String.matches("[0-9]{0,24}", value)
            data DecimalPart = { whole: WholeDigits, fraction: FractionDigits }
            data Coefficient = WholeDigits | DecimalPart

            data Fraction = { coefficient: DecimalPart }
            data Mixed = { coefficient: Coefficient }

            let coefficientText (c: Coefficient): String =
                match c with
                    | WholeDigits(w) -> w
                    | DecimalPart as d -> d.whole.value ++ "." ++ d.fraction.value

            behavior concrete : (f: Fraction) -> String
            let concrete (f) = coefficientText(f.coefficient)

            behavior either : (m: Mixed) -> String
            let either (m) = coefficientText(m.coefficient)

            data Up = { u: Int }
            data Down = { d: Int }
            data Flat
            data Slope = Up | Down
            data Ground = Slope | Flat

            let height (g: Ground): Int =
                match g with
                    | Up as up -> up.u
                    | Down as down -> down.d
                    | Flat -> 0

            data Rising = { slope: Up }
            data Sloped = { slope: Slope }

            behavior rising : (r: Rising) -> Int
            let rising (r) = height(r.slope)

            behavior sloped : (s: Sloped) -> Int
            let sloped (s) = height(s.slope)

            data Whole = { digits: WholeDigits }

            behavior whole : (x: Whole) -> String
            let whole (x) = coefficientText(x.digits)

            data On
            data Off
            data Flag = On | Off
            data Open = Flag
            data Opened = { flag: Open }

            let look (f: Flag): Int = match f with
                | On -> 1
                | Off -> 9

            behavior opened : (o: Opened) -> Int
            let opened (o) = look(o.flag.value)

            data Station = { code: String }
            data Hospital = { code: String }
            data Renkei
            data OnceKind = Station | Hospital
            data VisitKind = OnceKind | Renkei

            let visitText (k: VisitKind): String =
                match k with
                    | OnceKind as x ->
                        match x with
                            | Station as s -> s.code
                            | Hospital as h -> h.code
                    | Renkei -> ""

            data Request = { kind: OnceKind }
            data Visit = { kind: VisitKind }
            data Linked = { kind: Renkei }

            behavior once : (r: Request) -> String
            let once (r) = visitText(r.kind)

            behavior visit : (v: Visit) -> String
            let visit (v) = visitText(v.kind)

            behavior linked : (l: Linked) -> String
            let linked (l) = visitText(l.kind)
            """;

    /**
     * The reproduction: a field already a {@code DecimalPart} handed to a helper over
     * {@code Coefficient}, which matches it and reads the constrained fields of the case.
     *
     * <p>Measured whole. The arm the declaration already decides is no column, and the one it
     * leaves no value for is a rule no row is owed — the answer a condition the source settles the
     * other way gets, and not a rule this compiler could not name.
     */
    @Test
    void aConcreteFieldHandedToASumHelperIsMeasured() {
        Compilation c = Compilation.ofDocuments(Map.of("model.sou", WIDENED), Set.of(),
                ModulePath.EMPTY);
        c.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        c.answerEverything();
        assertEquals(List.of(), c.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList(), "the model is measured");

        DecisionEvidence decided = c.db().ask(new Adequacy.Decides(c.modules().get(0))).value()
                .get("render");
        assertNotNull(decided, "the behavior's rules are read");
        List<DecisionReading.Ruled> rules = decided.read().found();
        assertTrue(rules.stream().allMatch(DecisionReading.Ruled::whole),
                () -> "every rule is named whole: " + rules);
        assertEquals(1, rules.stream()
                        .filter(each -> each.states().neverComesOut().isPresent()).count(),
                () -> "one rule goes through the arm no value of the field takes: " + rules);
    }

    /** A field the declaration already makes the case is the location it names, unnarrowed. */
    @Test
    void anArmOnACaseTheFieldAlreadyIsNamesTheField() {
        assertEquals(Set.of("f.coefficient.whole", "f.coefficient.fraction"),
                underTheField(named("concrete"), "f.coefficient"));
    }

    /** A field the declaration leaves either case is narrowed by each arm, as it always was. */
    @Test
    void anArmOnAFieldOfSeveralCasesNarrowsIt() {
        Set<String> under = underTheField(named("either"), "m.coefficient");
        assertTrue(under.containsAll(Set.of("m.coefficient@DecimalPart.whole",
                        "m.coefficient@DecimalPart.fraction")),
                () -> "the case's fields are under the case: " + under);
        assertTrue(under.stream().anyMatch(each -> each.startsWith("m.coefficient@WholeDigits")),
                () -> "and the other arm narrows to the other case: " + under);
    }

    /**
     * Through a sum whose case is a sum: what a value can be is the leaves under it, so a field of
     * one leaf is that leaf under any arm naming it, and a field of the inner sum is narrowed to
     * each of its leaves and never to the case beside it.
     */
    @Test
    void whatAFieldCanBeIsTheLeavesUnderItsType() {
        assertEquals(Set.of("r.slope.u"), underTheField(named("rising"), "r.slope"),
                "a field that is one leaf is read unnarrowed, and nothing under the other leaf");
        assertEquals(Set.of("s.slope@Up", "s.slope@Up.u", "s.slope@Down", "s.slope@Down.d"),
                underTheField(named("sloped"), "s.slope"),
                "a field of the inner sum is narrowed to the leaf each arm selects");
    }

    /**
     * A name the value wears is asked as well as what is under it, since taking a newtype's
     * {@code value} is no step and the path does not say which of the two an arm matched.
     *
     * <p>A field declared as a newtype that is a case is that case, so only the other arm is out
     * of reach. A field declared as a newtype over a sum is matched as the sum under the name, so
     * neither arm is.
     */
    @Test
    void anArmIsAskedOfEveryNameTheValueWears() {
        assertEquals(Set.of(), underTheField(named("whole"), "x.digits"),
                "a field that is the case is named unnarrowed: what is under its name is no value"
                        + " the arm can be matching");
        assertEquals(1, outOfReach("whole"),
                "a field that is the case leaves only the other arm out of reach");
        assertEquals(0, outOfReach("opened"),
                "a field holding the sum under a name of its own leaves every arm in reach");
    }

    /**
     * An arm naming a case that is itself a sum is asked as the leaves it covers.
     *
     * <p>Such a case is one narrowing of nothing, so asked as one narrowing it had no question to
     * put to the declaration. A field the declaration leaves only those leaves is the case already:
     * the arm's name stands at the field, and the arms under it narrow the field to each leaf. A
     * field the declaration leaves none of them is never the case, and the rules through the arm
     * are rules no row is owed.
     */
    @Test
    void aFieldAlreadyACaseOverSeveralLeavesIsNarrowedByTheArmsUnderIt() {
        assertEquals(Set.of("r.kind@Station", "r.kind@Station.code", "r.kind@Hospital",
                        "r.kind@Hospital.code"),
                underTheField(named("once"), "r.kind"));
        assertEquals(1, outOfReach("once"), "only the arm beside the case is out of reach");
    }

    /** The other side of the one above: a field none of the case's leaves. */
    @Test
    void aFieldNoneOfTheLeavesOfACaseIsOutOfReachThroughIt() {
        assertEquals(2, outOfReach("linked"),
                "a field none of the case's leaves is out of reach through each arm under it");
    }

    /** And a field the declaration leaves every case, which the arms divide as they always did. */
    @Test
    void aFieldOfEveryCaseHasEveryArmInReach() {
        assertEquals(0, outOfReach("visit"));
    }

    /** How many of {@code behavior}'s rules go through an arm no value of the input takes. */
    private static long outOfReach(String behavior) {
        Compilation c = Compilation.ofSource(NAMED, "Main");
        c.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        c.answerEverything();
        DecisionEvidence decided = c.db().ask(new Adequacy.Decides(c.modules().get(0))).value()
                .get(behavior);
        assertNotNull(decided, () -> "the rules of " + behavior + " are read");
        return decided.read().found().stream()
                .filter(each -> each.states().neverComesOut().isPresent()).count();
    }

    /** The locations below {@code field} the body names, spelled. */
    private static Set<String> underTheField(List<TermPath> named, String field) {
        return named.stream().map(TermPath::toString)
                .filter(each -> each.startsWith(field) && !each.equals(field))
                .collect(Collectors.toSet());
    }

    /** Every location {@code behavior}'s body names, read the way its measurement reads it. */
    private static List<TermPath> named(String behavior) {
        Compilation compilation = Compilation.ofSource(NAMED, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, () -> "the model under test writes " + behavior);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get(behavior);
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(), inputs.declared(rules),
                checked.elementBindings().get(behavior), inputs.dependencies());
        return InputDemand.of(body, reads, rules.symbols(), rules.newtypes()).paths();
    }
}
