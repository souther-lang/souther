package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A quotient by a constant is arithmetic the reading composes, and what the constant is is what the
 * divisor was read as.
 *
 * <p>A quotient is exact, so {@code x / 3} weighs its position by a third and there is nothing left
 * over for the form to fail to say. That is what puts a divide in this grammar at all: an operation
 * whose fraction went somewhere the form could not name would be a value of its own beside the
 * position, and a rule written over it would relate two numbers rather than draw a line through one.
 *
 * <p><b>Constant is read and not spelled.</b> Every expression that comes to a number is one,
 * because what the reading has is the form the divisor came to and a form with no coefficients is a
 * number whatever wrote it. Matched against a written literal instead, naming a divisor would take
 * the line away — which is a rule about how a model is typed out rather than about what it says.
 *
 * <p>And the two shapes outside the fragment are here for what they are, and not as the shapes
 * somebody thought of: a divisor with a position in it, and a position the whole quotient is taken
 * under. The second is the one a scalar multiply would admit from either side, so it says that this
 * rule is not that one read symmetrically.
 *
 * <p>Read off the reading itself rather than off a report below it. What a comparison cuts is what
 * this is about, and everything a reader sees is downstream of it: a line at the place next to the
 * one the model states is still a line, and a report holding one would look like a report holding
 * the other.
 */
class AQuotientIsALineWhereItsDivisorIsAConstantTest {

    private static final String MODEL = """
            module example.quotient

            data Low = { v: Int }
            data High = { v: Int }
            data Level = Low | High

            behavior written : (x: Int) -> Level
                constructs Low, High
            let written (x) = if x / 2 < 30 then Low { v = 1 } else High { v = 2 }
            example written
                | "under" : (1) -> Low { v = 1 }

            behavior computed : (x: Int) -> Level
                constructs Low, High
            let computed (x) = if x / (1 + 1) < 30 then Low { v = 1 } else High { v = 2 }
            example computed
                | "under" : (1) -> Low { v = 1 }

            behavior named : (x: Int) -> Level
                constructs Low, High
            let named (x) = {
                let two = 2
                if x / two < 30 then Low { v = 1 } else High { v = 2 }
            }
            example named
                | "under" : (1) -> Low { v = 1 }

            behavior byAPosition : (x: Int, y: Int) -> Level
                constructs Low, High
            let byAPosition (x, y) = if x / y < 30 then Low { v = 1 } else High { v = 2 }
            example byAPosition
                | "under" : (1, 1) -> Low { v = 1 }

            behavior anInverse : (x: Int) -> Level
                constructs Low, High
            let anInverse (x) = if 1 / x < 30 then Low { v = 1 } else High { v = 2 }
            example anInverse
                | "under" : (1) -> Low { v = 1 }

            behavior byNought : (x: Int) -> Level
                constructs Low, High
            let byNought (x) = if x / 0 < 30 then Low { v = 1 } else High { v = 2 }
            example byNought
                | "under" : (1) -> Low { v = 1 }

            behavior aWrittenCoefficient : (x: Int, y: Int) -> Level
                constructs Low, High
            let aWrittenCoefficient (x, y) =
                if y < -1 / 3 * x + 30 then Low { v = 1 } else High { v = 2 }
            example aWrittenCoefficient
                | "under" : (1, 1) -> Low { v = 1 }

            behavior aNamedCoefficient : (x: Int, y: Int) -> Level
                constructs Low, High
            let aNamedCoefficient (x, y) = {
                let slope = -1 / 3
                if y < slope * x + 30 then Low { v = 1 } else High { v = 2 }
            }
            example aNamedCoefficient
                | "under" : (1, 1) -> Low { v = 1 }

            behavior aFractionalLattice : (x: Int) -> Level
                constructs Low, High
            let aFractionalLattice (x) = if 1 / 3 * x < 2 then Low { v = 1 } else High { v = 2 }
            example aFractionalLattice
                | "under" : (0) -> Low { v = 1 }
            """;

    /**
     * A quotient by a written constant weighs the position, and the line is where the exact
     * quotient puts it.
     *
     * <p>{@code x / 2 < 30} keeps every whole number under sixty and gives away sixty itself. A
     * reading carrying the quotient as a number of its own would draw a line on that number and not
     * on {@code x}, and one carrying the half as the nearest whole number would draw it somewhere
     * else on {@code x}.
     */
    @Test
    void aQuotientByAConstantWeighsThePositionItDivides() {
        assertEquals(List.of("x 59|60 belongs=ABOVE"), cutsOf("written"));
    }

    /**
     * And which divisors are constant follows from what each was read as.
     *
     * <p>Three spellings of one divisor: written out, computed from written numbers, and given a
     * name. The first is the measurement — a pair agreeing that nothing was read would agree just as
     * well — and the other two are what must not differ from it.
     */
    @Test
    void aDivisorIsConstantByWhatItReadsAsAndNotByHowItIsSpelled() {
        assertFalse(cutsOf("written").isEmpty(), "the written divisor draws a line");
        assertEquals(cutsOf("written"), cutsOf("computed"), "a divisor worked out from written"
                + " numbers is the number it comes to");
        assertEquals(cutsOf("written"), cutsOf("named"), "and a divisor given a name is the number"
                + " the name was given");
    }

    /**
     * A divisor with a position in it is no constant, and neither is a quotient taken under one.
     *
     * <p>Said as the rule being reported unread rather than as nothing being there. Those are
     * opposite facts about a model — one says this compiler fell short and the other says the model
     * draws no line — and a reading that had lost every quotient would answer the second to both.
     *
     * <p>The inverse is the one that says this rule is not a scalar multiply read symmetrically. A
     * product is linear from either side and admits {@code 2 * x} as readily as {@code x * 2}; a
     * quotient admits one side, and {@code 1 / x} is the side it does not.
     */
    @Test
    void aDivisorWithAPositionInItIsNoConstant() {
        assertEquals(List.of(), cutsOf("byAPosition"));
        assertEquals(List.of(), cutsOf("anInverse"));
        assertFalse(reasonsOf("byAPosition").isEmpty(),
                "a rule this could not read is reported as one");
        assertFalse(reasonsOf("anInverse").isEmpty(),
                "and so is a quotient taken under a position");
        assertEquals(List.of(), reasonsOf("written"),
                "where the quotient is read there is nothing to report");
    }

    /**
     * And a divisor of nought is no constant either, for a reason of its own.
     *
     * <p>Every other constant has a reciprocal to scale by. This one has none, and the operation it
     * was written in answers nothing wherever it is reached — so there is no value for a form to be
     * about, and one composed here would state an arithmetic meaning for an expression that computes
     * no number.
     */
    @Test
    void aDivisorOfNoughtIsNoConstant() {
        assertEquals(List.of(), cutsOf("byNought"));
    }

    /**
     * An exact coefficient reaches the form as the number it is, whether it was written where it
     * weighs or given a name first.
     *
     * <p>A third is no number a model can write out, so a form carrying it as one would be carrying
     * the nearest number that can be — and the line a rule draws is what every reader below is
     * derived from, so the whole report would be about a model nobody wrote.
     */
    @Test
    void anExactCoefficientReachesTheFormAsTheNumberItIs() {
        List<String> written = cutsOf("aWrittenCoefficient");

        assertEquals(1, written.size(), written.toString());
        assertEquals("LinearForm[constant=0, coefs={x=1/3, y=1}]",
                written.get(0).substring(0, written.get(0).indexOf(" on ")));
        assertEquals(written, cutsOf("aNamedCoefficient"),
                "a coefficient reached through a name is the coefficient");
    }

    /**
     * And a quantity whose own lattice is a third apart is cut where that lattice reaches.
     *
     * <p>{@code 1 / 3 * x < 2} holds of every whole number under six and of no other, which is a
     * line on {@code x} and not on a number a third of it. Beside the cases above because it is a
     * different one: those put a line at a fraction on a whole-numbered quantity, and this makes the
     * quantity itself fractional — a reading that carried a cut exactly and a lattice approximately
     * would pass those and fail this.
     */
    @Test
    void aQuantityALatticeOfThirdsReachesIsCutWhereItReaches() {
        assertEquals(List.of("x 5|6 belongs=ABOVE"), cutsOf("aFractionalLattice"));
        assertNotEquals(cutsOf("aFractionalLattice"), cutsOf("written"),
                "the two quotients are two lines");
    }

    /**
     * What each of a behavior's comparisons cuts, which is the affine reading itself.
     *
     * <p>Read off the reading rather than built here, for the reason the reading exists: a test that
     * assembled one would be a second account of what the names on the way meant.
     */
    private static List<String> cutsOf(String behavior) {
        Compilation compilation = read();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        souther.compiler.query.Bodies.Elaborated checked =
                compilation.db().ask(new souther.compiler.query.Bodies.Checked(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(each -> each.name().equals(behavior)).findFirst().orElseThrow();
        Core body = checked.behaviorBodies().get(spec.name());
        GuardThresholds.Guards guards = GuardThresholds.of(behavior,
                checked.analysisBodies().get(spec.name()), body, checked.plan(),
                compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior), rules);
        List<String> out = new java.util.ArrayList<>();
        guards.thresholds().forEach(each ->
                out.add(each.term() + " " + each.parts().below() + "|" + each.parts().above()
                        + " belongs=" + each.valueBelongs()));
        guards.between().forEach(each -> out.add(quantityOf(each.cuts().of())
                + " at " + each.cuts().at() + " " + each.cuts().claim()));
        return out.stream().sorted().toList();
    }

    /** What the report says about each rule it could not read, without the citation that differs
     *  between two spellings of one rule. */
    private static List<String> reasonsOf(String behavior) {
        Map<String, PartitionEvidence> all =
                measured().db().ask(new Adequacy.Coverage("example.quotient")).value();
        return all.get(behavior).notRead().stream()
                .map(found -> found instanceof PartitionEvidence.NotRead.ARule rule
                        ? rule.finding().at() + " " + rule.finding().why() : found.toString())
                .sorted()
                .toList();
    }

    /**
     * The model, compiled once for every question put to it.
     *
     * <p>One source and nine behaviors, and each of the readings below asks about one of them —
     * compiled where it is asked, the class pays for the whole model once per question. Read when a
     * question asks rather than in an initialiser, so a model that stopped compiling fails the
     * reading that met it instead of taking every method down with the class.
     */
    private static Compilation read() {
        if (compiled == null) {
            compiled = Compilation.ofSource(MODEL, "Main");
            compiled.answerEverything();
        }
        return compiled;
    }

    /** The same, measured, which is a second compilation because the report is what it is for. */
    private static Compilation measured() {
        if (reported == null) {
            reported = Compilation.ofSource(MODEL, "Main");
            reported.measure(Adequacy.Asked.fullReport());
            reported.answerEverything();
        }
        return reported;
    }

    private static Compilation compiled;

    private static Compilation reported;

    /** Let go at the end, so the fork's later classes do not carry this model's answers. */
    @AfterAll
    static void release() {
        compiled = null;
        reported = null;
    }

    private static String quantityOf(BorderQuantity quantity) {
        return switch (quantity) {
            case BorderQuantity.OfACoordinate one -> one.term() + " on " + one.of();
            case BorderQuantity.OverAForm form -> form.form() + " on " + form.on();
            case BorderQuantity.Apart apart ->
                    apart.onTerm() + " vs " + apart.againstTerm()
                            + " on " + apart.on() + ", " + apart.against();
        };
    }
}
