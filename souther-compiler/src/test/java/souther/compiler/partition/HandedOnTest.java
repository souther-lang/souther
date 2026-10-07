package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a parameter's value hands on is read off what the boundary built, and off what the row
 * writes only where nothing built it.
 *
 * <p>Held where the two disagree, since that is the case the rule is for: a value written one way
 * and built as another hands on what was built, whether the row wrote the position or named a
 * value that has it.
 */
class HandedOnTest {

    private static final String MODULE = """
            module example.handed

            data Request = { level: Int, note: Int }
            data Res = { n: Int }

            behavior f : (request: Request) -> Res
            """;

    private static final TermPath LEVEL = TermPath.of("request").then("level");

    private static final InputReading READ = read();

    private static final Generator.CandidateCheck.Built BUILT_AT_FIVE =
            new Generator.CandidateCheck.Built.Value(new ObservedValue.Constructed(
                    TypeSymbols.declared(new TypeKey("example.handed", "Request")),
                    Map.of("level", new ObservedValue.Integer(5),
                            "note", new ObservedValue.Integer(0))));

    /** Built at a level the row did not write there: what was built is handed on. */
    @Test
    void whatWasBuiltIsHandedOnOverWhatTheRowWrites() {
        assertEquals(Map.of(LEVEL, "5"),
                texts(handedOn(BUILT_AT_FIVE, Map.of(LEVEL, FixtureTemplate.integer(1)))));
    }

    /** And where the row writes nothing there — a value named rather than written out. */
    @Test
    void whatWasBuiltIsHandedOnWhereTheRowWritesNothingThere() {
        assertEquals(Map.of(LEVEL, "5"), texts(handedOn(BUILT_AT_FIVE, Map.of())));
    }

    /** Nothing built it, so what the row writes is all there is. */
    @Test
    void whereNothingBuiltItWhatTheRowWritesIsHandedOn() {
        assertEquals(Map.of(LEVEL, "1"),
                texts(handedOn(new Generator.CandidateCheck.Built.NothingBuiltIt(),
                        Map.of(LEVEL, FixtureTemplate.integer(1)))));
    }

    /** And a position the row does not write is then nothing to hand over. */
    @Test
    void whereNothingBuiltItAPositionTheRowDoesNotWriteIsNotHandedOn() {
        assertInstanceOf(HandedOn.Came.NotWritable.class,
                handedOn(new Generator.CandidateCheck.Built.NothingBuiltIt(), Map.of()));
    }

    @Test
    void aRefusedValueHandsOnNothing() {
        assertInstanceOf(HandedOn.Came.Refused.class,
                handedOn(new Generator.CandidateCheck.Built.Refused("no"),
                        Map.of(LEVEL, FixtureTemplate.integer(1))));
    }

    private static HandedOn.Came handedOn(Generator.CandidateCheck.Built built,
                                          Map<TermPath, FixtureTemplate> written) {
        return HandedOn.of(built, () -> written, Set.of(LEVEL), BehaviorInputs.of(READ),
                RuleReadingContext.unshared(READ.rules(), ReadAs.THE_COMPILATION_DOES));
    }

    private static Map<TermPath, String> texts(HandedOn.Came came) {
        Map<TermPath, FixtureTemplate> at =
                assertInstanceOf(HandedOn.Came.Values.class, came, () -> "handed on: " + came)
                        .at();
        Map<TermPath, String> out = new LinkedHashMap<>();
        at.forEach((path, value) -> out.put(path, value.text()));
        return out;
    }

    private static InputReading read() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain domain = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(domain, "the model under test compiles");
        return domain.reading(rules);
    }
}
