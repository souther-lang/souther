package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code match} over a sum whose case is a sum (#966, spec §sum-data, §match).
 *
 * <p>Such a case is transparent as a value — anything of the inner sum is of the outer one — and an
 * arm may name it or name what is under it. What tells the {@code match} apart from what it left
 * out is which of the values the subject can be nobody answered for, so an arm naming the inner sum
 * and an arm naming one of its leaves are the same kind of arm and are counted the same way.
 *
 * <p>The generated code needed nothing for this. An arm tests the class its case is written as, and
 * a leaf's class already carries the interface of every sum that reaches it.
 */
class CompileMatchOverANestedSumTest {

    private static final String DECLARATIONS = """
            module demo

            data Station  = { at: String }
            data Hospital = { at: String }
            data Renkei   = { at: String }
            data OnceKind  = Station | Hospital
            data VisitKind = OnceKind | Renkei
            """;

    private static String feeOf(String arms) {
        return DECLARATIONS + """

                behavior fee : (k: VisitKind) -> Int

                let fee (k) =
                    match k with
                """ + arms;
    }

    private Object fee(String arms, String leaf) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(feeOf(arms)),
                getClass().getClassLoader());
        Object value = Codecs.decoded(loader, "demo.VisitKind", Map.of("type", leaf, "at", "x"));
        Object behavior = Emitted.behavior(loader, "demo", "fee").getConstructor().newInstance();
        return Codecs.apply(behavior, value);
    }

    /** The arms the issue could not write. Each leaf of the nesting is one arm. */
    @Test
    void everyLeafOfTheNestingIsOneArm() throws Exception {
        String arms = """
                        | Station -> 1
                        | Hospital -> 2
                        | Renkei -> 3
                """;
        assertEquals(1L, fee(arms, "Station"));
        assertEquals(2L, fee(arms, "Hospital"));
        assertEquals(3L, fee(arms, "Renkei"));
    }

    /** And the arms it could write still work: naming the inner sum answers for both of its leaves. */
    @Test
    void namingTheInnerSumAnswersForWhatIsUnderIt() throws Exception {
        String arms = """
                        | OnceKind -> 1
                        | Renkei -> 2
                """;
        assertEquals(1L, fee(arms, "Station"));
        assertEquals(1L, fee(arms, "Hospital"));
        assertEquals(2L, fee(arms, "Renkei"));
    }

    /** A leaf arm and an arm over the rest of the nesting in one match, which is the point of it:
     *  one column of a table that applies to one leaf only stops being a nested match. */
    @Test
    void aLeafArmAndAnArmOverTheRestStandTogether() throws Exception {
        String arms = """
                        | Station -> 1
                        | Hospital -> 2
                        | Renkei -> 3
                """;
        assertEquals(2L, fee(arms, "Hospital"));

        String grouped = """
                        | Station -> 1
                        | Hospital | Renkei -> 9
                """;
        assertEquals(1L, fee(grouped, "Station"));
        assertEquals(9L, fee(grouped, "Hospital"));
        assertEquals(9L, fee(grouped, "Renkei"));
    }

    /**
     * An arm answering for a value an earlier arm already answered for is refused.
     *
     * <p>{@code Station} is under {@code OnceKind}, so the two arms both answer for a station and
     * which of them takes it would be decided by nothing the author wrote. Held against what the
     * arms cover and not against how they are spelled, which is the only way this one is visible.
     */
    @Test
    void anArmAnsweringForWhatAnEarlierArmDidIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile(feeOf("""
                        | OnceKind -> 1
                        | Station -> 2
                        | Renkei -> 3
                """)));
        assertEquals("E1204", refused.diagnostic().code());
        assertTrue(refused.diagnostic().said().toString().contains("Station"),
                () -> "the report names the value both arms answer for, said " + refused.diagnostic().said());
        assertEquals(1, refused.diagnostic().secondary().size(),
                "and points at the arm that answers for it first");
    }

    /**
     * One arm naming one case twice is refused as a mistake in that arm.
     *
     * <p>Not as two arms answering for one value. An arm answers for the union of its alternatives,
     * so the second {@code Station} changes nothing about what the arm takes — which is exactly why
     * it has to be reported: the line was written for a reason that did not happen.
     */
    @Test
    void oneArmNamingOneCaseTwiceIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile(feeOf("""
                        | Station | Station -> 1
                        | Hospital -> 2
                        | Renkei -> 3
                """)));
        assertEquals("E1209", refused.diagnostic().code());
        assertTrue(refused.diagnostic().said().toString().contains("Station"));
    }

    /**
     * And so is an alternative another alternative of the same arm already answers for.
     *
     * <p>The same defect one level up, and the one the author is more likely to have made: naming a
     * leaf beside the sum above it usually means the case they meant is not the case they named.
     */
    @Test
    void anAlternativeCoveredByAnotherOfTheSameArmIsRefused() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile(feeOf("""
                        | Station | OnceKind -> 1
                        | Renkei -> 2
                """)));
        assertEquals("E1209", refused.diagnostic().code());
        String said = refused.diagnostic().said().toString();
        assertTrue(said.contains("Station") && said.contains("OnceKind"),
                () -> "the report names the alternative that adds nothing and the one that covers "
                        + "it, said " + said);
    }

    /** An arm whose alternatives each add something is not that, however deep they sit. */
    @Test
    void alternativesThatEachAddSomethingStandTogether() throws Exception {
        String arms = """
                        | Station | Renkei -> 1
                        | Hospital -> 2
                """;
        assertEquals(1L, fee(arms, "Station"));
        assertEquals(1L, fee(arms, "Renkei"));
        assertEquals(2L, fee(arms, "Hospital"));
    }

    /**
     * What no arm answered for is named the way the model declares it.
     *
     * <p>The check is settled over the values, because that is what an arm answers for. The report
     * is not owed in those terms: the model wrote {@code OnceKind} to say something, and a report
     * of its two leaves is about a declaration nobody made.
     */
    @Test
    void whatNoArmAnsweredForIsNamedTheWayTheModelDeclaresIt() {
        assertEquals(List.of("OnceKind"), unanswered("""
                        | Renkei -> 3
                """));
    }

    /** And is opened where only part of a declared case is missing, since the case is not. */
    @Test
    void aCaseOnlyPartlyMissingIsOpenedRatherThanNamed() {
        assertEquals(List.of("Station"), unanswered("""
                        | Hospital -> 2
                        | Renkei -> 3
                """));
    }

    /**
     * Both at once, in the order the model declares them.
     *
     * <p>{@code AB} is missing entirely and is named; {@code CD} is missing only {@code D} and is
     * opened. A report that did one of the two everywhere would be wrong about the other half.
     */
    @Test
    void whatIsNamedAndWhatIsOpenedComeInTheOrderTheModelDeclaresThem() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data A = { at: String }
                data B = { at: String }
                data C = { at: String }
                data D = { at: String }
                data AB  = A | B
                data CD  = C | D
                data All = AB | CD

                behavior fee : (k: All) -> Int

                let fee (k) =
                    match k with
                        | C -> 1
                """));
        assertEquals("E1201", refused.diagnostic().code());
        assertEquals(List.of("AB", "D"), hinted(refused));
    }


    /**
     * An anonymous union states no order, so the report is not left holding the set's.
     *
     * <p>A union is a set. Which order it iterates in follows from how it was built and not from
     * anything about the program, so a report reading it would move between two runs of one
     * compiler. The order is put on the union in one place; both the values a match answers for and
     * the names a report says are read from it, and writing the members the other way round is the
     * same union.
     */
    @Test
    void aReportOverAnAnonymousUnionReadsInAnOrderTheCompilerDecided() {
        assertEquals(List.of("B", "C"), unansweredOfUnion("A | B | C"));
        assertEquals(List.of("B", "C"), unansweredOfUnion("C | A | B"),
                "the union written the other way round is the same union");
    }

    /** And the subject the report names it on is the same union, however it was written. */
    @Test
    void theUnionAReportNamesReadsInThatOrderToo() {
        assertEquals(saidOverUnion("A | B | C"), saidOverUnion("C | A | B"),
                "what the match is said to be on is the union, not the order it was written in");
        assertTrue(saidOverUnion("C | A | B").contains("A | B | C"),
                () -> "in the order the union states its members, said " + saidOverUnion("C | A | B"));
    }

    private String saidOverUnion(String members) {
        return refusedOverUnion(members).diagnostic().said().toString();
    }

    private List<String> unansweredOfUnion(String members) {
        return hinted(refusedOverUnion(members));
    }

    private CompileException refusedOverUnion(String members) {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data A = { at: String }
                data B = { at: String }
                data C = { at: String }
                data Seen = { at: String }

                behavior pick : (s: Seen) -> %s

                behavior fee : (s: Seen) -> Int

                let fee (s) =
                    match pick(s) with
                        | A -> 1
                """.formatted(members)));
        assertEquals("E1201", refused.diagnostic().code());
        return refused;
    }

    /**
     * Where two cases of one subject both cover what is missing, the first is named and the second
     * is opened.
     *
     * <p>A value may be a case of more than one declaration, so {@code AB} and {@code ABC} both
     * cover {@code A} and {@code B}. Naming both would report a value twice and would offer two
     * arms that cannot both be written — they answer for one value, which a match refuses. So the
     * names that come back share nothing: {@code AB}, and then what is left of {@code ABC}.
     */
    @Test
    void whereTwoCasesBothCoverWhatIsMissingTheNamesStillShareNothing() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data A = { at: String }
                data B = { at: String }
                data C = { at: String }
                data D = { at: String }
                data AB  = A | B
                data ABC = A | B | C
                data All = AB | ABC | D

                behavior fee : (k: All) -> Int

                let fee (k) =
                    match k with
                        | D -> 1
                """));
        assertEquals("E1201", refused.diagnostic().code());
        assertEquals(List.of("AB", "C"), hinted(refused));
    }

    /** The cases a `match` was refused for not answering, as its report names them. */
    private List<String> unanswered(String arms) {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(feeOf(arms)));
        assertEquals("E1201", refused.diagnostic().code());
        return hinted(refused);
    }

    private static List<String> hinted(CompileException refused) {
        String cases = refused.diagnostic().notes().stream()
                .map(n -> String.valueOf(souther.compiler.diag.msg.MessageValues.of(n.said()).get("cases")))
                .findFirst().orElseThrow();
        return List.of(cases.split(", "));
    }

    /**
     * A type covering part of the subject is an arm, whether or not the subject reaches it.
     *
     * <p>{@code OtherKind} is no case of {@code VisitKind} and nothing declares a path from one to
     * the other; what makes it an arm is that every value it is, is a value the subject can be.
     * That is the reading assignability already takes, and there is no value that could tell the
     * two apart — a station is a station however many declarations group it.
     */
    @Test
    void aTypeCoveringPartOfTheSubjectIsAnArmHoweverItWasDeclared() throws Exception {
        String source = """
                module demo

                data Station  = { at: String }
                data Hospital = { at: String }
                data Renkei   = { at: String }
                data OnceKind  = Station | Hospital
                data OtherKind = Station | Hospital
                data VisitKind = OnceKind | Renkei

                behavior fee : (k: VisitKind) -> Int

                let fee (k) =
                    match k with
                        | OtherKind -> 1
                        | Renkei -> 2
                """;
        assertDoesNotThrow(() -> Compiler.compile(source));
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                getClass().getClassLoader());
        Object value = Codecs.decoded(loader, "demo.VisitKind", Map.of("type", "Station", "at", "x"));
        Object behavior = Emitted.behavior(loader, "demo", "fee").getConstructor().newInstance();
        assertEquals(1L, Codecs.apply(behavior, value),
                "the arm has to take the value at run time and not only pass the check");
    }

    /** And a type covering nothing the subject can be is still not an arm. */
    @Test
    void aTypeTheSubjectCannotBeIsNoArm() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Station  = { at: String }
                data Hospital = { at: String }
                data Renkei   = { at: String }
                data Clinic   = { at: String }
                data OnceKind  = Station | Hospital
                data VisitKind = OnceKind | Renkei

                behavior fee : (k: VisitKind) -> Int

                let fee (k) =
                    match k with
                        | Clinic -> 1
                        | Renkei -> 2
                """));
        assertEquals("E1203", refused.diagnostic().code());
    }

    /**
     * Naming the subject itself is the arm that answers for everything.
     *
     * <p>A consequence of the rule and not an exception to it: inclusion holds of equal sets, so a
     * type every value of which the subject can be includes the subject. Refusing it would mean
     * adding that a candidate must not be the subject, which is a rule about names in a check that
     * is otherwise entirely about values — and assignability reads it the same way, where a type is
     * assignable to itself before anything about cases is asked.
     *
     * <p>So the language has an arm that answers for every value, reached by naming the subject.
     * It is not a wildcard in the sense of matching whatever happens to be left: it answers for
     * everything, so nothing can follow it.
     */
    @Test
    void namingTheSubjectItselfAnswersForEveryValueOfIt() throws Exception {
        String arms = """
                        | VisitKind -> 1
                """;
        assertEquals(1L, fee(arms, "Station"));
        assertEquals(1L, fee(arms, "Hospital"));
        assertEquals(1L, fee(arms, "Renkei"));
    }

    /** And nothing can follow it, since it left no value for another arm to answer for. */
    @Test
    void nothingCanFollowTheArmThatAnsweredForEverything() {
        assertThrows(CompileException.class, () -> Compiler.compile(feeOf("""
                        | VisitKind -> 1
                        | Renkei -> 2
                """)));
    }


    /**
     * Where two alternatives answer alike, the later one is the one that adds nothing.
     *
     * <p>{@code OnceKind} and {@code OtherKind} answer for the same two values, so neither covers
     * the other by being wider and the tie is broken by where they are written: an arm reads left
     * to right, and the first is where a reader learns what it answers for.
     */
    @Test
    void whereTwoAlternativesAnswerAlikeTheLaterOneAddsNothing() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Station  = { at: String }
                data Hospital = { at: String }
                data Renkei   = { at: String }
                data OnceKind  = Station | Hospital
                data OtherKind = Station | Hospital
                data VisitKind = OnceKind | Renkei

                behavior fee : (k: VisitKind) -> Int

                let fee (k) =
                    match k with
                        | OnceKind | OtherKind -> 1
                        | Renkei -> 2
                """));
        assertEquals("E1209", refused.diagnostic().code());
        assertEquals("AnAlternativeAddsNothingToThisArm[alternative=OtherKind, covering=OnceKind]",
                refused.diagnostic().said().toString(),
                "the later of two that answer alike is the one that adds nothing");
    }


    /**
     * A case named twice is reported as that even where a covering alternative stands between them.
     *
     * <p>The two findings are asked as two questions and the more particular one is asked first.
     * Found in one walk, which of them an author is told would follow from whichever pair the walk
     * reached — here {@code Station} inside {@code OnceKind} comes before the second
     * {@code Station} — and the arm would be reported as covering something while never mentioning
     * that a name is in it twice.
     */
    @Test
    void aCaseNamedTwiceIsReportedAsThatEvenBesideACoveringAlternative() {
        CompileException refused = assertThrows(CompileException.class, () -> Compiler.compile(feeOf("""
                        | Station | OnceKind | Station -> 1
                        | Renkei -> 2
                """)));
        assertEquals("E1209", refused.diagnostic().code());
        assertEquals("ThisArmNamesOneCaseTwice[caseName=Station]",
                refused.diagnostic().said().toString(),
                "the slip is what is said, not the covering that also holds");
    }

}
