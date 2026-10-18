package souther.compiler.partition;

import souther.compiler.inputs.CasesLeft;
import souther.compiler.meaning.DecisionSubject;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fork on a value the body computed asks the input one question, whichever way the body
 * reaches the input.
 *
 * <p>Taking an arm of such a fork comes to the input being some case of a position. That is what
 * the arm means for the input, and it answers a question about the input: the arms between them
 * divide it, and a second fork on the same position divided the same way is the same question. It is
 * no answer to a question about the computed value, whose cases are another type's.
 */
class AForkOnAComputedValueAnswersAboutTheInputTest {

    private static final String KINDS = """
            module example.kinds

            data A
            data B
            data C
            data Kind = A | B | C
            data Hot
            data Cold
            data Flag = Hot | Cold
            data Done
            data Other
            """;

    private static final String SUMS = """
            module repro.rematched_sum_fork

            data OpenCursor
            data ClosedCursor
            data Cursor = OpenCursor | ClosedCursor
            data InvalidParts
            data WholeParts
            data Parts = InvalidParts | WholeParts
            data OpenKind
            data ClosedKind
            data CursorKind = OpenKind | ClosedKind
            data InvalidKind
            data WholeKind
            data PartsKind = InvalidKind | WholeKind
            data Reject
            data Accept
            data Route = Reject | Accept

            let cursorKind (cursor: Cursor): CursorKind =
                match cursor with
                    | OpenCursor -> OpenKind
                    | ClosedCursor -> ClosedKind

            let partsKind (parts: Parts): PartsKind =
                match parts with
                    | InvalidParts -> InvalidKind
                    | WholeParts -> WholeKind

            let classify (cursor: CursorKind, parts: PartsKind): Route =
                match cursor with
                    | ClosedKind -> Reject
                    | OpenKind
                        -> match parts with
                            | InvalidKind -> Reject
                            | WholeKind -> Accept

            behavior consume : (cursor: Cursor, parts: Parts) -> Route
            let consume (cursor, parts) =
                match classify(cursorKind(cursor), partsKind(parts)) with
                    | Reject -> Reject
                    | Accept
                        -> match cursor with
                            | OpenCursor
                                -> match parts with
                                    | WholeParts -> Accept
                                    | InvalidParts -> unreachable "Accept contains WholeParts"
                            | ClosedCursor -> unreachable "Accept contains OpenCursor"
            """;

    /**
     * The route is decided from the kinds, and the inputs are matched again inside it.
     *
     * <p>The fork on the cursor's kind is a question about the cursor, answered by its two cases;
     * the fork inside the route that matches the cursor again asks the same question and is the same
     * column. The same holds of the parts.
     */
    @Test
    void theKindsAndTheInputsAreOneQuestionAboutEachInput() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(SUMS, "consume");

        Set<DecisionCondition.ACase> columns = casesOf(rules);
        assertEquals(Set.of(Set.of("OpenCursor", "ClosedCursor"),
                        Set.of("InvalidParts", "WholeParts")),
                columns.stream().map(AForkOnAComputedValueAnswersAboutTheInputTest::spelled)
                        .collect(Collectors.toSet()),
                "a column apiece for the cursor and the parts, answered in their own cases: "
                        + columns);
        assertEquals(2, columns.size(), "asking an input again is the same column");
    }

    /** A rotation answers each arm with a different case of the input than the arm names. */
    @Test
    void aHelperThatMovesTheCasesAroundIsAskedAsTheInputsOwnCases() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(KINDS + """

                let rotate (kind: Kind): Kind =
                    match kind with
                        | A -> B
                        | B -> C
                        | C -> A

                behavior f : (kind: Kind) -> Done | Other
                let f (kind) =
                    match rotate(kind) with
                        | A -> Done
                        | B -> Other
                        | C -> Done
                """, "f");

        Set<DecisionCondition.ACase> columns = casesOf(rules);
        assertEquals(1, columns.size(), "one question about the one input: " + columns);
        assertEquals(Set.of("A", "B", "C"), spelled(columns.iterator().next()),
                "the arms are the cases of the kind the input has");
    }

    /** A helper that makes two cases one gives an arm more than one case of the input. */
    @Test
    void aHelperThatJoinsCasesGivesAnArmTheCasesItJoined() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(KINDS + """

                let flag (kind: Kind): Flag =
                    match kind with
                        | A -> Hot
                        | B -> Hot
                        | C -> Cold

                behavior f : (kind: Kind) -> Done | Other
                let f (kind) =
                    match flag(kind) with
                        | Hot -> Done
                        | Cold -> Other
                """, "f");

        Set<DecisionCondition.ACase> columns = casesOf(rules);
        assertEquals(1, columns.size(), "one question about the one input: " + columns);
        assertEquals(Set.of("{A|B}", "C"), spelled(columns.iterator().next()),
                "the arm for Hot is the two cases that make a Hot");
    }

    /** What a fork on the input itself is, for the same input read both ways. */
    @Test
    void theInputMatchedDirectlyIsTheSameColumnAsTheInputMatchedThroughAHelper() {
        List<DecisionRule> direct = DecisionReadings.readToTheEnd(KINDS + """

                behavior f : (kind: Kind) -> Done | Other
                let f (kind) =
                    match kind with
                        | A -> Done
                        | B -> Other
                        | C -> Done
                """, "f");
        List<DecisionRule> rotated = DecisionReadings.readToTheEnd(KINDS + """

                let rotate (kind: Kind): Kind =
                    match kind with
                        | A -> B
                        | B -> C
                        | C -> A

                behavior f : (kind: Kind) -> Done | Other
                let f (kind) =
                    match rotate(kind) with
                        | A -> Done
                        | B -> Other
                        | C -> Done
                """, "f");

        assertEquals(spelled(casesOf(direct).iterator().next()),
                spelled(casesOf(rotated).iterator().next()),
                "one input divided into its three cases whichever way the body asks");
        assertEquals(casesOf(direct).iterator().next().of(),
                casesOf(rotated).iterator().next().of(), "and asked of the same subject");
    }

    /**
     * A position the declarations leave fewer cases is divided as it is when it is matched
     * directly: the case they exclude is an answer of the one question as much as the others.
     */
    @Test
    void aPositionTheDeclarationsNarrowIsDividedAsItIsWhenMatchedDirectly() {
        String declared = KINDS + """

                data Pick = { kind: Kind }
                    invariant notC = match kind with
                        | A -> true
                        | B -> true
                        | C -> false
                """;
        List<DecisionRule> direct = DecisionReadings.readToTheEnd(declared + """

                behavior f : (pick: Pick) -> Done | Other
                let f (pick) =
                    match pick.kind with
                        | A -> Done
                        | B -> Other
                        | C -> Done
                """, "f");
        List<DecisionRule> rotated = DecisionReadings.readToTheEnd(declared + """

                let rotate (kind: Kind): Kind =
                    match kind with
                        | A -> B
                        | B -> C
                        | C -> A

                behavior f : (pick: Pick) -> Done | Other
                let f (pick) =
                    match rotate(pick.kind) with
                        | A -> Done
                        | B -> Other
                        | C -> Done
                """, "f");

        assertEquals(1, casesOf(direct).size());
        assertEquals(1, casesOf(rotated).size(), "one question: " + casesOf(rotated));
        assertEquals(spelled(casesOf(direct).iterator().next()),
                spelled(casesOf(rotated).iterator().next()),
                "what the declarations leave the position, whichever way the body asks");
    }

    /** A fork on what a dependency answered stays a question about that answer. */
    @Test
    void aForkOnWhatADependencyAnsweredIsStillAboutTheAnswer() {
        List<DecisionRule> rules = DecisionReadings.readToTheEnd(KINDS + """

                behavior look : (at: Int) -> Kind

                behavior f : (at: Int) -> Done | Other
                    depends on look
                let f (at, look) =
                    match look(at) with
                        | A -> Done
                        | B -> Other
                        | C -> Done
                """, "f");

        Set<DecisionCondition.ACase> columns = casesOf(rules);
        assertEquals(1, columns.size(), "one question: " + columns);
        DecisionCondition.ACase column = columns.iterator().next();
        assertTrue(column.of() instanceof DecisionSubject.AnAnswer,
                "the answer is the subject, and not a position of the input: " + column);
        assertEquals(Set.of("A", "B", "C"), spelled(column));
    }

    private static Set<DecisionCondition.ACase> casesOf(List<DecisionRule> rules) {
        return rules.stream()
                .flatMap(rule -> rule.consulted().keySet().stream())
                .filter(DecisionCondition.ACase.class::isInstance)
                .map(DecisionCondition.ACase.class::cast)
                .collect(Collectors.toCollection(LinkedHashSet::new));
    }

    private static Set<String> spelled(DecisionCondition.ACase column) {
        return column.answers().stream().map(CasesLeft::spelled)
                .collect(Collectors.toCollection(LinkedHashSet::new));
    }
}
