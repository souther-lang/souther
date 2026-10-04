package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.BoundaryInput;
import souther.compiler.check.RuleReadings;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeReachName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a value comes to through the decoder is worked out once for the classes it is built against.
 *
 * <p>A search tries one candidate at every point of a border and under every way of standing the
 * dependencies in, and what the decoder makes of the candidate is the same each time — it is asked
 * about the position and the fixture and about nothing the search is doing. Whether the value
 * stands at the point is the other half and is asked of what comes back, at each point; nothing
 * here keeps that.
 */
class AValueIsBuiltOnceHoweverManyPointsAskAboutItTest {

    private static final BoundaryInput INT = new BoundaryInput.Scalar(LeafScalar.INT);

    private static final BoundaryInput TEXT = new BoundaryInput.Scalar(LeafScalar.STRING);

    /** One position and one fixture, asked about again and again: the decoder runs once. */
    @Test
    void theSameValueAtTheSamePositionIsBuiltOnce() {
        Counting source = new Counting(new BoundaryValues.Built.Value(new ObservedValue.Integer(7)));
        FixturesAtTheBoundary remembered = FixturesAtTheBoundary.remembering(source);

        BoundaryValues.Built first = remembered.build(INT, seven());
        for (int again = 0; again < 3; again++) {
            assertSame(first, remembered.build(INT, seven()));
        }
        assertEquals(1, source.asked.size(), "one position, one fixture, one answer");
    }

    /**
     * Two occurrences of one name are one value to ask about.
     *
     * <p>Their trees differ — each carries the reference the run composed — and a row writes the
     * same line for both, which is what the decoder is asked about.
     */
    @Test
    void twoOccurrencesOfOneNameAreBuiltOnce() {
        Counting source = new Counting(new BoundaryValues.Built.Value(new ObservedValue.Integer(7)));
        FixturesAtTheBoundary remembered = FixturesAtTheBoundary.remembering(source);
        ReachName.Own standard = new ReachName.Own(new ValueName.Helper("g", "standard"));
        FixtureTemplate first = FixtureTemplate.named(standard, new FixtureReferenceOrigin(0));
        FixtureTemplate second = FixtureTemplate.named(standard, new FixtureReferenceOrigin(1));
        assertNotEquals(first.value(), second.value(), "two references, composed apart");

        assertSame(remembered.build(INT, first), remembered.build(INT, second));
        assertEquals(1, source.asked.size(), "one line a row writes, one answer");
    }

    /** A refusal is the decoder's answer about the fixture as much as a value is, and is kept. */
    @Test
    void aRefusalIsKeptTheWayAValueIs() {
        Counting source = new Counting(new BoundaryValues.Built.Refused("not this one"));
        FixturesAtTheBoundary remembered = FixturesAtTheBoundary.remembering(source);

        remembered.build(INT, seven());
        remembered.build(INT, seven());

        assertEquals(1, source.asked.size());
    }

    /**
     * And what was thrown is not.
     *
     * <p>A runtime that would not link, or an evaluation that ran out, says something about this run
     * and nothing about the fixture — so the next asking finds out again.
     */
    @Test
    void whatWasThrownIsAskedAgain() {
        Counting source = new Counting(null);
        FixturesAtTheBoundary remembered = FixturesAtTheBoundary.remembering(source);

        assertThrows(LinkageError.class, () -> remembered.build(INT, seven()));
        assertThrows(LinkageError.class, () -> remembered.build(INT, seven()));

        assertEquals(2, source.asked.size());
    }

    /** Another fixture, or the same fixture at another position, is another question. */
    @Test
    void anotherFixtureOrAnotherPositionIsAskedAboutAsItself() {
        Counting source = new Counting(new BoundaryValues.Built.Value(new ObservedValue.Integer(7)));
        FixturesAtTheBoundary remembered = FixturesAtTheBoundary.remembering(source);

        remembered.build(INT, seven());
        remembered.build(INT, FixtureTemplate.integer(8));
        remembered.build(TEXT, seven());

        assertEquals(3, source.asked.size());
    }

    /**
     * And the classes a module's values are built against are asked this way.
     *
     * <p>Built again on every asking, the same fixture would come back as a new value each time — an
     * equal one, and the work of the decoder done over.
     */
    @Test
    void theClassesOfAModuleAnswerOnceForEachValue() {
        Compilation compilation = Compilation.ofSource("""
                module g

                data Ok
                data Amount = Int

                let standard = Amount(7)

                behavior read : (x: Int) -> Ok
                behavior charge : (a: Amount) -> Ok
                """, "Main");
        compilation.answerEverything();
        FixturesAtTheBoundary building = Adequacy.constructing(compilation.db(), "g");
        assertNotNull(building, "the module has classes to build against");

        BoundaryValues.Built built = building.build(INT, seven());
        assertInstanceOf(BoundaryValues.Built.Value.class, built);
        assertSame(built, building.build(INT, seven()));

        BoundaryValues.Built refused = building.build(INT, FixtureTemplate.string("seven"));
        assertInstanceOf(BoundaryValues.Built.Refused.class, refused);
        assertSame(refused, building.build(INT, FixtureTemplate.string("seven")));

        BoundaryInput amount = compilation.signatures("g").get("charge").ins().get(0);
        ReachName.Own standard = new ReachName.Own(new ValueName.Helper("g", "standard"));
        BoundaryValues.Built named = building.build(amount,
                FixtureTemplate.named(standard, new FixtureReferenceOrigin(0)));
        assertInstanceOf(BoundaryValues.Built.Value.class, named,
                "a name the module states is built as what it names");
        assertSame(named, building.build(amount,
                FixtureTemplate.named(standard, new FixtureReferenceOrigin(1))),
                "and another occurrence of the name is the same value to ask about");
    }

    /**
     * What a value's own type says of it is kept the same way, by the type and the text.
     *
     * <p>A search asks it of every value it offers once its first assignment is refused, and the
     * same values stand at the same types in every search of a module.
     */
    @Test
    void whatAValuesOwnTypeSaysIsAskedOnceForEachTypeAndValue() {
        Counting source = new Counting(new BoundaryValues.Built.Refused("not this one"));
        FixturesAtTheBoundary remembered = FixturesAtTheBoundary.remembering(source);

        BoundaryValues.OnItsOwn first = remembered.buildAlone(Type.INT, seven());
        assertEquals(first, remembered.buildAlone(Type.INT, seven()));
        remembered.buildAlone(Type.INT, FixtureTemplate.integer(8));
        remembered.buildAlone(Type.STRING, seven());

        assertEquals(BoundaryValues.OnItsOwn.REFUSED, first);
        assertEquals(3, source.asked.size(), "one answer per type and value");
    }

    /**
     * A module's classes say which values a declared type refuses on its own, and say nothing of a
     * type nothing decodes on its own.
     *
     * <p>The second is what keeps an optional field's {@code None} on offer: an optional is decoded
     * by the record holding it, and asked about alone it has no decoder to refuse anything.
     */
    @Test
    void theClassesOfAModuleSayWhatADeclaredTypeRefusesOnItsOwn() {
        Compilation compilation = Compilation.ofSource("""
                module g

                data Ok
                data Code = String
                    invariant String.matches("[A-Z]{3}", value)

                behavior read : (c: Code) -> Ok
                """, "Main");
        compilation.answerEverything();
        FixturesAtTheBoundary building = Adequacy.constructing(compilation.db(), "g");
        assertNotNull(building, "the module has classes to build against");
        Type.Ref code = assertInstanceOf(Type.Ref.class,
                compilation.signatures("g").get("read").ins().get(0).type());
        TypeReachName.Written written = assertInstanceOf(TypeReachName.Written.class,
                RuleReadings.of(compilation, "g").symbols().scope().reach(code.name()));

        assertEquals(BoundaryValues.OnItsOwn.BUILT, building.buildAlone(code,
                FixtureTemplate.newtype(written, FixtureTemplate.string("ABC"))));
        assertEquals(BoundaryValues.OnItsOwn.REFUSED, building.buildAlone(code,
                FixtureTemplate.newtype(written, FixtureTemplate.string("x"))));
        assertEquals(BoundaryValues.OnItsOwn.NO_DECODER_OF_ITS_OWN,
                building.buildAlone(Type.option(code),
                        FixtureTemplate.newtype(written, FixtureTemplate.string("x"))));
    }

    private static FixtureTemplate seven() {
        return FixtureTemplate.integer(7);
    }

    /** A decoder that says one thing, and writes down every time it was asked; throws where that
     *  one thing is nothing. */
    private static final class Counting implements BoundaryValues {

        private final Built answer;
        private final List<String> asked = new ArrayList<>();

        Counting(Built answer) {
            this.answer = answer;
        }

        @Override
        public Built build(BoundaryInput at, Hir.Expr fixture) {
            asked.add(at + " " + fixture);
            if (answer == null) {
                throw new LinkageError("no runtime");
            }
            return answer;
        }

        @Override
        public OnItsOwn buildAlone(Type type, Hir.Expr fixture) {
            asked.add(Type.show(type) + " " + fixture);
            return switch (answer) {
                case null -> throw new LinkageError("no runtime");
                case Built.Value _ -> OnItsOwn.BUILT;
                case Built.Refused _ -> OnItsOwn.REFUSED;
            };
        }
    }
}
