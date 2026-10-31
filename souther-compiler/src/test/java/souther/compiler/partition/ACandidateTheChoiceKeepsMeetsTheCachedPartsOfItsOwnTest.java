package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.ElementsMet;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Conclusion;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Of the candidates a choice tries, the parts met are the parts of the candidate it keeps, whether
 * that candidate made the reading of a part or took it from one a candidate before it made.
 *
 * <p>Asked of the choice itself ({@link RuleChoice}) over a list that candidates add to and the
 * choice takes back out of, with a part read by the first candidate and taken by the second. The
 * first stops, so the second is tried while the first's parts are still met; the second is kept,
 * and the first's parts are taken back out.
 */
class ACandidateTheChoiceKeepsMeetsTheCachedPartsOfItsOwnTest {

    private static final Core NODE = new Core.Int(1, Type.INT, new SourcePos(1, 1));
    private static final InputReads READS =
            InputReads.ofWhatIsDeclared(Map.of(), DeclaredInput.NONE);

    /** A reader whose parts met are the strings in a list. */
    private static final class AScene implements SharedReads.Scene<Integer, Integer, String> {

        final List<String> met = new ArrayList<>();

        @Override
        public boolean mayShare() {
            return true;
        }

        @Override
        public Integer inputs() {
            return 0;
        }

        @Override
        public boolean sameInputs(Integer then, Integer now, boolean askedAggregates) {
            return then.equals(now);
        }

        @Override
        public Integer guards() {
            return 0;
        }

        @Override
        public boolean sameGuards(Integer then, Integer now) {
            return then.equals(now);
        }

        @Override
        public ElementsMet elementsMet() {
            return ElementsMet.NONE;
        }

        @Override
        public int metCount() {
            return met.size();
        }

        @Override
        public List<String> metSince(int from) {
            return met.subList(from, met.size());
        }

        @Override
        public void meetAgain(List<String> parts) {
            met.addAll(parts);
        }

        @Override
        public int aggregatesAsked() {
            return 0;
        }
    }

    private final AScene scene = new AScene();
    private final SharedReads<Integer, Integer, String, String> reads = new SharedReads<>(scene);

    private String readThePart() {
        return reads.shared(NODE, READS, "part", () -> {
            scene.met.add("the part");
            return "read";
        }, _ -> true);
    }

    private Supplier<Derivation> candidateThatReadsThePartAnd(Derivation then) {
        return () -> {
            readThePart();
            return then;
        };
    }

    @Test
    void theCandidateKeptMeetsThePartItTookFromACandidateSetAside() {
        Derivation stopped = new Derivation.Stopped(new WhyUnread.NotArithmetic(), false);
        Derivation read = new Derivation.WrittenOut(true);

        Derivation chosen = RuleChoice.firstThatReadsIt(
                List.of(candidateThatReadsThePartAnd(stopped), candidateThatReadsThePartAnd(read)),
                scene.met, Conclusion.reusing());

        assertSame(read, chosen);
        assertEquals(List.of("the part"), scene.met,
                "the second candidate took the part, and the first's record of it is gone");
    }

    @Test
    void theCandidateKeptThatReadThePartItselfLeavesItMetOnce() {
        Derivation read = new Derivation.WrittenOut(true);

        Derivation chosen = RuleChoice.firstThatReadsIt(
                List.of(candidateThatReadsThePartAnd(read)), scene.met, Conclusion.reusing());

        assertSame(read, chosen);
        assertEquals(List.of("the part"), scene.met);
    }
}
