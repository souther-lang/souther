package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.InputUse;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position nothing a behavior states reads is owed no row at its classes, and keeps them.
 *
 * <p>A row at one class of such a position gives the answer a row at any other class gives, so it
 * checks nothing a row beside it did not. The classes are still the model's: the count has them and
 * the rows are counted against them. What goes is the obligation, and only where every tree the
 * behavior states was read and none of them reads the value. A value read without being told apart
 * — copied into the answer, or taken whole — is owed a row at each class.
 */
class APositionNothingReadsIsOwedNoRowTest {

    /** `upgrade` is carried and never read; `grip` is what the behavior decides on. */
    private static final String UNREAD = """
            module example.unread

            data OneHanded
            data TwoHanded
            data Grip = OneHanded | TwoHanded
            data Upgradable
            data NotUpgradable
            data Upgrade = Upgradable | NotUpgradable
            data Weapon = { grip: Grip, upgrade: Upgrade }
            data Equipped
            data Refused

            behavior judge : (weapon: Weapon) -> Equipped | Refused

            let judge (weapon) =
                match weapon.grip with
                    | OneHanded -> Equipped
                    | TwoHanded -> Refused

            example judge
                | "one-handed" : (Weapon { grip = OneHanded, upgrade = NotUpgradable }) -> Equipped
                | "two-handed" : (Weapon { grip = TwoHanded, upgrade = NotUpgradable }) -> Refused
            """;

    @Test
    void aFieldNothingReadsIsNotRead() {
        PartitionEvidence partition = coverageOf(UNREAD, "example.unread");

        assertInstanceOf(InputUse.NotRead.class, axis(partition, "weapon.upgrade").use(),
                () -> "only `grip` is taken off `weapon`: " + partition.axes());
        assertInstanceOf(InputUse.Read.class, axis(partition, "weapon.grip").use(),
                () -> "`grip` is matched on: " + partition.axes());
    }

    /** No finding at it, nothing handed to a generation, and the classes still counted. */
    @Test
    void itIsOwedNoRowAndKeepsItsClasses() {
        Compilation compilation = compiled(UNREAD);
        PartitionEvidence partition = coverageOf(compilation, "example.unread");
        PartitionEvidence.AxisCoverage upgrade = axis(partition, "weapon.upgrade");

        assertEquals(List.of("Upgradable", "NotUpgradable"), upgrade.classes(),
                "the classes are the model's whether or not anything reads them");
        assertEquals(List.of("Upgradable"), upgrade.uncovered().stream()
                        .map(PartitionEvidence.AxisClass::name).toList(),
                "and what the rows reached of them is what it was");
        assertEquals(List.of(), upgrade.owed(), "a row at either class checks nothing more");
        assertTrue(partition.classesOwed().isEmpty(),
                () -> "nothing to hand a generation: " + partition.classesOwed());
        List<Adequacy.Finding> findings = findingsOf(compilation, "example.unread");
        assertTrue(findings.stream().noneMatch(each ->
                        each.about() instanceof About.AClassNoRowIsIn),
                () -> "no class is found missing: " + findings);
    }

    /** The report counts the class and says why it asks for no row there. */
    @Test
    void theReportSaysWhyNoRowIsAskedFor() {
        String human = report(UNREAD);

        assertTrue(human.contains("equivalence partitions 3/4"),
                () -> "the denominator is the model's: " + human);
        assertFalse(human.contains("is in `Upgradable`"),
                () -> "no row is asked for at `Upgradable`: " + human);
        assertTrue(human.contains("weapon.upgrade holds 2 classes and nothing this behavior states"
                        + " reads it, so no row is owed at any of them"),
                () -> "and the reason is said: " + human);
        assertFalse(human.contains("weapon.upgrade holds 2 classes and this behavior"),
                () -> "nothing beside it says the body tells them apart or not: " + human);
    }

    /** An input of its own nothing reads is owed no row at a case either. */
    @Test
    void anInputOfItsOwnNothingReadsIsOwedNoCase() {
        Compilation compilation = compiled("""
                module example.own

                data TooShort
                data TooLong
                data WrongCase
                data Refusal = TooShort | TooLong | WrongCase

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """);
        PartitionEvidence partition = coverageOf(compilation, "example.own");
        List<Adequacy.Finding> findings = findingsOf(compilation, "example.own");

        assertInstanceOf(InputUse.NotRead.class, axis(partition, "why").use(),
                () -> "`why` is never read: " + partition.axes());
        assertTrue(findings.stream().noneMatch(each ->
                        each.about() instanceof About.ACaseNoRowAppliesItTo
                                || each.about() instanceof About.AClassNoRowIsIn),
                () -> "neither the case nor the class is found missing: " + findings);
    }

    /**
     * A value carried into the answer is read and told apart by nothing, and is owed a row at each
     * class.
     */
    @Test
    void aValueCarriedIntoTheAnswerIsOwedARowAtEachClass() {
        String model = """
                module example.carried

                data OneHanded
                data TwoHanded
                data Grip = OneHanded | TwoHanded
                data Upgradable
                data NotUpgradable
                data Upgrade = Upgradable | NotUpgradable
                data Weapon = { grip: Grip, upgrade: Upgrade }
                data Equipped = { upgrade: Upgrade }
                data Refused

                behavior judge : (weapon: Weapon) -> Equipped | Refused
                    constructs Equipped

                let judge (weapon) =
                    match weapon.grip with
                        | OneHanded -> Equipped { upgrade = weapon.upgrade }
                        | TwoHanded -> Refused

                example judge
                    | (Weapon { grip = OneHanded, upgrade = NotUpgradable })
                        -> Equipped { upgrade = NotUpgradable }
                    | (Weapon { grip = TwoHanded, upgrade = NotUpgradable }) -> Refused
                """;
        Compilation compilation = compiled(model);
        PartitionEvidence partition = coverageOf(compilation, "example.carried");
        String human = report(model);

        assertInstanceOf(InputUse.Read.class, axis(partition, "weapon.upgrade").use(),
                () -> "the value is copied into the answer: " + partition.axes());
        assertTrue(findingsOf(compilation, "example.carried").stream().anyMatch(each ->
                        each.about() instanceof About.AClassNoRowIsIn(var missing)
                                && missing.name().equals("Upgradable")),
                "a row at `Upgradable` gives another answer and is owed");
        assertTrue(human.contains("weapon.upgrade holds 2 classes and this behavior reads it"
                        + " without telling them apart"),
                () -> "and the line beside it says it is read: " + human);
    }

    /** A value taken whole reads every field under it. */
    @Test
    void aValueTakenWholeReadsEveryFieldUnderIt() {
        PartitionEvidence partition = coverageOf("""
                module example.whole

                data OneHanded
                data TwoHanded
                data Grip = OneHanded | TwoHanded
                data Upgradable
                data NotUpgradable
                data Upgrade = Upgradable | NotUpgradable
                data Weapon = { grip: Grip, upgrade: Upgrade }
                data Equipped = { weapon: Weapon }
                data Refused

                behavior judge : (weapon: Weapon) -> Equipped | Refused
                    constructs Equipped

                let judge (weapon) =
                    match weapon.grip with
                        | OneHanded -> Equipped { weapon = weapon }
                        | TwoHanded -> Refused

                example judge
                    | (Weapon { grip = OneHanded, upgrade = NotUpgradable })
                        -> Equipped { weapon = Weapon { grip = OneHanded, upgrade = NotUpgradable } }
                    | (Weapon { grip = TwoHanded, upgrade = NotUpgradable }) -> Refused
                """, "example.whole");

        assertInstanceOf(InputUse.Read.class, axis(partition, "weapon.upgrade").use(),
                () -> "`weapon` is put into the answer as it is: " + partition.axes());
    }

    /**
     * A field every case of a sum has is read without naming a case, and reads the field under each
     * of them.
     */
    @Test
    void aFieldEveryCaseHasIsReadUnderEachCase() {
        PartitionEvidence partition = coverageOf("""
                module example.shared

                data Yes
                data No
                data Flag = Yes | No
                data Common = { flag: Flag }
                data A = { ...Common, a: Int }
                data B = { ...Common, b: Int }
                data Q = A | B
                data Req = { q: Q }

                behavior judge : (r: Req) -> String
                let judge (r) =
                    match r.q.flag with
                        | Yes -> "yes"
                        | No -> "no"

                example judge
                    | (Req { q = A { flag = Yes, a = 0 } }) -> "yes"
                """, "example.shared");

        assertInstanceOf(InputUse.Read.class, axis(partition, "r.q@A.flag").use(),
                () -> "the flag is read whichever case `q` is: " + partition.axes());
        assertInstanceOf(InputUse.Read.class, axis(partition, "r.q@B.flag").use(),
                () -> "the flag is read whichever case `q` is: " + partition.axes());
    }

    /** A clause of the behavior reads what it names, whatever the body does. */
    @Test
    void aClauseReadsWhatItNames() {
        PartitionEvidence partition = coverageOf("""
                module example.stated

                data OneHanded
                data TwoHanded
                data Grip = OneHanded | TwoHanded
                data Upgradable
                data NotUpgradable
                data Upgrade = Upgradable | NotUpgradable
                data Weapon = { grip: Grip, upgrade: Upgrade }
                data Equipped
                data Refused

                behavior judge : (weapon: Weapon) -> Equipped | Refused
                    ensures Equipped -> weapon.grip == OneHanded || weapon.upgrade == Upgradable

                let judge (weapon) =
                    match weapon.grip with
                        | OneHanded -> Equipped
                        | TwoHanded -> Refused

                example judge
                    | (Weapon { grip = OneHanded, upgrade = NotUpgradable }) -> Equipped
                    | (Weapon { grip = TwoHanded, upgrade = NotUpgradable }) -> Refused
                """, "example.stated");

        assertInstanceOf(InputUse.Read.class, axis(partition, "weapon.upgrade").use(),
                () -> "the `ensures` reads `upgrade`: " + partition.axes());
    }

    /** A behavior nothing implements reads what its implementation will, which is not known. */
    @Test
    void aBehaviorWithNoBodyIsNotKnownToReadNothing() {
        Compilation compilation = compiled("""
                module example.injected

                data Yes
                data No
                data Flag = Yes | No

                data Ok = { n: Int }

                behavior judge : (a: Flag) -> Ok

                example judge
                    | (Yes) -> Ok { n = 0 }
                """);
        PartitionEvidence partition = coverageOf(compilation, "example.injected");

        assertInstanceOf(InputUse.NotKnown.class, axis(partition, "a").use(),
                () -> "nothing was read: " + partition.axes());
        assertTrue(partition.classesOwed().stream()
                        .anyMatch(each -> each.name().equals("No")),
                () -> "and the class is owed: " + partition.classesOwed());
    }

    /**
     * A name bound to the value reads nothing by being bound: what the body reads through it is
     * what is read, a field taken off it in one model and the whole of it in the other.
     */
    @Test
    void aNameBoundToTheValueReadsWhatIsReadThroughIt() {
        String declarations = """
                data OneHanded
                data TwoHanded
                data Grip = OneHanded | TwoHanded
                data Upgradable
                data NotUpgradable
                data Upgrade = Upgradable | NotUpgradable
                data Weapon = { grip: Grip, upgrade: Upgrade }
                data Refused
                """;
        PartitionEvidence aField = coverageOf("module example.alias\n\n" + declarations + """
                data Equipped

                behavior judge : (weapon: Weapon) -> Equipped | Refused

                let judge (weapon) = {
                    let w = weapon
                    match w.grip with
                        | OneHanded -> Equipped
                        | TwoHanded -> Refused
                }
                """, "example.alias");
        PartitionEvidence theWhole = coverageOf("module example.aliased\n\n" + declarations + """
                data Equipped = { weapon: Weapon }

                behavior judge : (weapon: Weapon) -> Equipped | Refused
                    constructs Equipped

                let judge (weapon) = {
                    let w = weapon
                    match w.grip with
                        | OneHanded -> Equipped { weapon = w }
                        | TwoHanded -> Refused
                }
                """, "example.aliased");

        assertInstanceOf(InputUse.NotRead.class, axis(aField, "weapon.upgrade").use(),
                () -> "only `grip` is taken off the name: " + aField.axes());
        assertInstanceOf(InputUse.Read.class, axis(aField, "weapon.grip").use(),
                () -> "`grip` is matched on through the name: " + aField.axes());
        assertInstanceOf(InputUse.Read.class, axis(theWhole, "weapon.upgrade").use(),
                () -> "the name is put into the answer as it is: " + theWhole.axes());
    }

    /**
     * A {@code match} on a value asks which case it is, which reads the position and nothing under
     * the case; what an arm reads through the name it binds is read.
     */
    @Test
    void aMatchReadsTheCaseAndAnArmReadsWhatItTakesOffItsName() {
        String declarations = """
                data Yes
                data No
                data Flag = Yes | No
                data A = { flag: Flag, a: Int }
                data B = { other: Flag, b: Int }
                data Q = A | B
                data Req = { q: Q }

                behavior judge : (r: Req) -> String
                """;
        PartitionEvidence theCase = coverageOf("module example.cased\n\n" + declarations + """
                let judge (r) =
                    match r.q with
                        | A -> "a"
                        | B -> "b"
                """, "example.cased");
        PartitionEvidence throughTheArm = coverageOf("module example.armed\n\n" + declarations + """
                let judge (r) =
                    match r.q with
                        | A as it ->
                            match it.flag with
                                | Yes -> "yes"
                                | No -> "no"
                        | B -> "b"
                """, "example.armed");

        assertInstanceOf(InputUse.Read.class, axis(theCase, "r.q").use(),
                () -> "which case `q` is, is asked: " + theCase.axes());
        assertInstanceOf(InputUse.NotRead.class, axis(theCase, "r.q@A.flag").use(),
                () -> "and nothing under the case is: " + theCase.axes());
        assertInstanceOf(InputUse.Read.class, axis(throughTheArm, "r.q@A.flag").use(),
                () -> "the arm takes `flag` off the name it binds: " + throughTheArm.axes());
        assertInstanceOf(InputUse.NotRead.class, axis(throughTheArm, "r.q@B.other").use(),
                () -> "and nothing takes `other` off `B`: " + throughTheArm.axes());
    }

    /** The document keeps the classes and what the rows reached, and says beside them why no row
     *  is asked for. */
    @Test
    void theDocumentKeepsTheClassesAndSaysTheyAreNotRead() throws Exception {
        Compilation compilation = compiled(UNREAD);
        JsonNode upgrade = null;
        for (JsonNode each : JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .get("modules").get(0).get("behaviors").get(0).get("partition").get("axes")) {
            if (each.get("path").asString().equals("weapon.upgrade")) {
                upgrade = each;
            }
        }
        JsonNode at = upgrade;

        assertTrue(at != null, "the document has the position");
        assertEquals("not_read", at.get("use").asString(), () -> at.toString());
        assertEquals(List.of("Upgradable", "NotUpgradable"),
                at.get("classes").valueStream().map(JsonNode::asString).toList(),
                () -> at.toString());
        assertEquals(List.of("NotUpgradable"),
                at.get("covered").valueStream().map(JsonNode::asString).toList(),
                () -> at.toString());
    }

    private static PartitionEvidence.AxisCoverage axis(PartitionEvidence partition, String name) {
        return partition.axes().stream().filter(each -> each.name().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("no position " + name + " among "
                        + partition.axes()));
    }

    private static List<Adequacy.Finding> findingsOf(Compilation compilation, String module) {
        return compilation.db().ask(new Adequacy.Findings(module)).value();
    }

    private static PartitionEvidence coverageOf(String model, String module) {
        return coverageOf(compiled(model), module);
    }

    private static PartitionEvidence coverageOf(Compilation compilation, String module) {
        return compilation.db().ask(new Adequacy.Coverage(module)).value().get("judge");
    }

    /**
     * The model, compiled and measured. Held to compiling without a diagnostic: a body that does not
     * check is no body, and what nothing reads in it would be said to be not known, which reads as
     * an answer about the body.
     */
    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).map(each -> each.diagnostic().code() + " "
                        + each.diagnostic().titleKey()).toList(),
                "the model under test compiles");
        return compilation;
    }

    private static String report(String model) {
        Compilation compilation = compiled(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
