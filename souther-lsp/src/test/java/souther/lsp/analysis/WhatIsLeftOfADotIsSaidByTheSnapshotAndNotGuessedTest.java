package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.LineIndex;
import souther.compiler.meta.ModulePath;
import souther.compiler.sites.MemberReceiver;
import souther.compiler.sites.SemanticSnapshot;
import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The parser reads {@code m.name} and {@code x.field} the same way, so what may be written after a
 * {@code .} is not a question the syntax answers. It is answered on the source as it stands
 * mid-edit, and the answer says which of the two the author is looking at.
 *
 * <p>The two are asked together because they pull the probe's rule in opposite directions. What may
 * be read off a repaired source is what was written before anything was put in, and the access
 * around the cursor never is: it runs to the end of the name the probe supplied. The receiver does —
 * a value's occurrence stops at the {@code .}, and so does a qualifier. So the rule is put to where
 * the receiver is written, which is what {@link MemberReceiver#writtenAt} carries.
 */
class WhatIsLeftOfADotIsSaidByTheSnapshotAndNotGuessedTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String LIB_URI = "file:///lib.sou";

    private static final String LIB = """
            module lib exposing ( Cost )

            data Cost = { value: Int }
            """;

    private static String model(String body) {
        return """
                module m

                import lib as l ( Cost )

                data Draft = { plannedCost: Cost }

                behavior submit : (request: Draft) -> Int
                let submit (request) = \
                """ + body;
    }

    @Test
    void aFieldTakenOffAValueIsAValueReceiver() {
        assertInstanceOf(MemberReceiver.UntypedValue.class,
                leftOfTheDot(model("request.plannedCost.\n")),
                "`request.plannedCost` is a value, and no declaration read here says its type yet");
    }

    @Test
    void anAliasIsAnsweredAsTheModuleItNames() {
        MemberReceiver receiver = leftOfTheDot(model("l.\n"));

        assertEquals(new MemberReceiver.Namespace.OfModule("lib", receiver.writtenAt()), receiver,
                "the alias is resolved here, so nothing downstream has to resolve `l` again");
    }

    @Test
    void aCursorOnNoAccessIsToldSo() {
        String text = model("request\n");
        Probed probed = probe(model("request.plannedCost.\n"));
        LineIndex lines = new LineIndex(text, new SourceId(MODEL_URI));

        assertTrue(probed.snapshot().memberReceiverAround(lines.posOf(0)).isEmpty(),
                "the first character of `module m` is in no field read");
    }

    /**
     * And what every answer here rests on is source the author wrote.
     *
     * <p>The other half — that the access around it is not — is what
     * {@code WhatIsAskedOfAHalfWrittenLineIsAskedOfWhatItSaysNowTest} holds, on the access node
     * itself. What is checked here is that the receiver an editor is handed clears the rule, which
     * is the thing that makes the receiver usable and the access not.
     */
    @Test
    void whatTheAnswerRestsOnIsSourceTheAuthorWrote() {
        for (String body : new String[]{"request.plannedCost.\n", "l.\n"}) {
            Probed probed = probe(model(body));
            assertTrue(probed.reading().mayBeRead(probed.receiver().writtenAt()),
                    "the receiver of `" + body.strip() + "` stops at the `.`, so it may be read");
        }
    }

    private record Probed(SemanticProbe.Reading reading, SemanticSnapshot snapshot,
                          MemberReceiver receiver) {}

    private static MemberReceiver leftOfTheDot(String text) {
        return probe(text).receiver();
    }

    /** The buffer with its half-written line finished off, and what the snapshot says about the
     *  access the cursor is in — which is the question an editor puts, cursor and all. */
    private static Probed probe(String text) {
        Map<String, String> joining = new LinkedHashMap<>();
        joining.put(LIB_URI, LIB);
        int cursor = text.lastIndexOf(".\n") + 1;
        SemanticProbe.Reading reading = new SemanticProbe().of(joining, Set.of(), ModulePath.EMPTY,
                MODEL_URI, text, cursor);
        if (reading == null) {
            throw new AssertionError("the half-written line is one the probe finishes off");
        }
        SemanticSnapshot snapshot = SemanticSnapshot.of(reading.compilation().db(), "m")
                .orElseThrow(() -> new AssertionError("the repaired source has a snapshot"));
        LineIndex lines = new LineIndex(text, new SourceId(MODEL_URI));
        MemberReceiver receiver = snapshot.memberReceiverAround(lines.posOf(cursor))
                .orElseThrow(() -> new AssertionError("nothing is written at the cursor"));
        return new Probed(reading, snapshot, receiver);
    }
}
