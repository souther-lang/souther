package souther.compiler.query;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What is known to sit in an answer and not mean anything by {@code equals}, and who sees it.
 *
 * <p>One register for both detectors. They see different things and both are needed — one walks a
 * store and asks each object what it is, the other holds two stores side by side and asks where they
 * come apart — but what a finding <em>is</em>, and which of the two ways out it takes, is one
 * judgement and is made here. Written twice, the two lists drift into two vocabularies for one fact.
 *
 * <p><b>A place and not a class.</b> An entry names the question, where in that answer the thing
 * sits, and what it is. Keyed by the class alone, a class already written down here turning up under
 * some other answer would be waved through as known; keyed by the place, it is a new place the debt
 * has reached and says so.
 *
 * <p><b>Two ways out and no third.</b> {@link Meaning} is what a thing is, and there are two of
 * them: something that says what it is, with what is wrong with how it says it, or something that
 * does something. A word for a thing nobody has read yet would be a third, and it is what let a
 * place stand here twice with no remedy attached — so there is none, and a walk meeting something
 * unread fails until somebody says which of the two it is.
 *
 * <p><b>Where it was seen is not what it is.</b> A finding is one finding however many detectors and
 * however many scenarios meet it, so the detector and the scenario are provenance beside the entry
 * rather than part of what it names. Held inside the identity, one thing seen twice would read as
 * two things — the same mistake as keying by class, from the other side.
 */
final class AnswerClosure {

    /**
     * What a thing is, which is the whole of the reading and takes one of two forms.
     *
     * <p>Written as one thing rather than as a kind beside a fault. What says a thing is a value is
     * the same reading that says what is wrong with it as it stands, so the two were never apart:
     * held as two words, a line could say a thing is a value and a way of asking at once, and a line
     * could say the reading got as far as the kind and stopped. Neither is a state anybody can act
     * on, and the second is what let a place stand here with no remedy attached.
     *
     * <p>So there is no word for an unread one. A thing nobody has read yet is not written down, and
     * the walk that meets it fails until somebody says which of these it is.
     */
    sealed interface Meaning {

        /** Something that says what it is, and what is wrong with how it says it. */
        record Value(ValueProblem problem) implements Meaning {}

        /** Something that does something, or that carries something that does. What such a thing is
         *  worth to whoever holds it turns on where it is held. */
        record Capability() implements Meaning {}
    }

    /** What is wrong with how a value says what it is. */
    enum ValueProblem {
        /** It defines no equality over what it says. */
        MISSING_EQUALITY,
        /**
         * Its equality is an address — its own, or its members'.
         *
         * <p>Its own word beside the one above because the work is different. Something with no
         * equality wants one written; something whose equality is an address has one already and it
         * answers the wrong question, so what it wants is to be held in something that means what it
         * says. Filed under the first, the second sends whoever picks it up to add a method beside
         * one that is already there.
         */
        IDENTITY_SEMANTICS
    }

    /** Something that says what it is and defines no equality over that. */
    private static final Meaning MISSING_EQUALITY =
            new Meaning.Value(ValueProblem.MISSING_EQUALITY);

    /** A way of asking something rather than an answer, so it is one object per store whatever it
     *  is compared with. */
    private static final Meaning CAPABILITY = new Meaning.Capability();

    /** What one of these is, in the words a reader of a failure gets. */
    private static String said(Meaning meaning) {
        return switch (meaning) {
            case Meaning.Value(ValueProblem problem) -> "VALUE/" + problem;
            case Meaning.Capability _ -> "CAPABILITY";
        };
    }

    /** Which walk met it. */
    enum Detector {
        /** One store walked, each object asked what it is. {@link AnswerWalk}. */
        ONE_ANSWER_WALKED,
        /** Two stores over one input compared. {@link Divergence}. */
        TWO_ANSWERS_COMPARED
    }

    /** What was compiled for it to be met in. */
    enum Scenario {
        /** The conformance corpus, analysed with everything measured. */
        VALID_CORPUS,
        /** A module the compiler has something to say about, so the reports half of an answer is not
         *  empty. Its own scenario because a corpus of valid models cannot reach it: an answer is
         *  what it holds and what was said getting there, and only one of those is exercised by a
         *  model nothing is said about. */
        A_MODULE_SPOKEN_ABOUT
    }

    /**
     * One thing in one place, and what it is.
     *
     * @param place the question it is under, where in that answer it sits, and the class of the
     *              thing or the array type
     * @param meaning what it is, which is also what the remedy follows from
     */
    record Identity(Locus.Place place, Meaning meaning) {}

    /** One detector meeting one identity in one scenario. */
    record Observation(Detector detector, Scenario scenario) implements Comparable<Observation> {

        @Override
        public int compareTo(Observation other) {
            int by = detector.compareTo(other.detector);
            return by != 0 ? by : scenario.compareTo(other.scenario);
        }

        @Override
        public String toString() {
            return detector + "/" + scenario;
        }
    }

    private record Known(Identity identity, Set<Observation> seenBy, String reason) {}

    private static Observation walked(Scenario scenario) {
        return new Observation(Detector.ONE_ANSWER_WALKED, scenario);
    }

    private static Observation compared(Scenario scenario) {
        return new Observation(Detector.TWO_ANSWERS_COMPARED, scenario);
    }

    private static final String CLASS_BYTES =
            "what a class is is its bytes, so a wrapper comparing them is what lets a module whose "
                    + "classes came out the same leave its readers alone. Five places and one thing "
                    + "to fix";

    private static final Set<Observation> BOTH_EVERYWHERE = Set.of(
            walked(Scenario.VALID_CORPUS), compared(Scenario.VALID_CORPUS),
            walked(Scenario.A_MODULE_SPOKEN_ABOUT), compared(Scenario.A_MODULE_SPOKEN_ABOUT));

    private static final Set<Observation> ONLY_WALKED = Set.of(
            walked(Scenario.VALID_CORPUS), walked(Scenario.A_MODULE_SPOKEN_ABOUT));

    /** A place, written the way a walk writes one. */
    private static Locus.Place at(String question, String offender, Locus.Step... steps) {
        return new Locus(List.of(steps)).of(question, offender);
    }

    /** A member step, by what the declaring type is called rather than what it is shown as. Two
     *  types of one short name are two types, and a place is told from a place by the first. */
    private static Locus.Step m(String owner, String name) {
        return new Locus.Step.Member(owner, name);
    }

    private static final String ANSWER = "souther.compiler.query.Answer";

    private static final Locus.Step ELEMENT = new Locus.Step.Element();
    private static final Locus.Step VALUE = new Locus.Step.MapValue();

    /**
     * The end itself, on the way to what is holding it.
     *
     * <p>Under the range and never beside it: one of these exists only where there is an end, and
     * the two of them are which side of the range they sit in. So the answer to comparing two is
     * {@code NarrowedBounds}'s own, which is written out and does compare the ends and the names —
     * a reader never reaches this one, and what it is missing is never the answer anybody gets.
     *
     * <p>Reached at all because the walk asks each object what it is rather than asking whoever
     * holds it. Which is the point of asking that way: the day something takes one of these out
     * from under the range that answers for it, this place is what says so.
     */
    private static Known narrowedEnd(String question, Observation met, Locus.Step... steps) {
        return new Known(new Identity(at(question, "souther.compiler.check.NarrowedEnd", steps),
                MISSING_EQUALITY), Set.of(met),
                "one end of what a reading leaves a position, with what is holding it. A value, and "
                        + "one nothing compares on its own: the range it sits in writes its own "
                        + "equality and reaches both ends through it");
    }

    private static Known bytes(String question, Locus.Step... steps) {
        return new Known(new Identity(at(question, "byte[]", steps), MISSING_EQUALITY),
                BOTH_EVERYWHERE, CLASS_BYTES);
    }

    private static final String Q = "souther.compiler.query.";

    private static final List<Known> KNOWN = List.of(
            bytes(Q + "Output$All", m(ANSWER, "value"), VALUE),
            bytes(Q + "Output$Classes", m(ANSWER, "value"), VALUE),
            bytes(Q + "Output$Evaluated", m(ANSWER, "value"),
                    m("souther.compiler.generated.EvaluationArtifact", "classes"), VALUE),
            bytes(Q + "Output$EvaluationLinked", m(ANSWER, "value"),
                    m("souther.compiler.generated.EvaluationArtifact", "classes"), VALUE),
            // The one of the five a module on its own does not reach: nothing is linked against
            // where there is nothing to link against.
            new Known(new Identity(at(Q + "Output$Linked", "byte[]", m(ANSWER, "value"), VALUE),
                    MISSING_EQUALITY),
                    Set.of(walked(Scenario.VALID_CORPUS), compared(Scenario.VALID_CORPUS)),
                    CLASS_BYTES),
            new Known(new Identity(at(Q + "Names$ModuleScope", Q + "Db",
                    m(ANSWER, "value"), m("souther.compiler.check.Scoping$Scoped", "values"), m("souther.compiler.check.Resolve$Values", "elsewhere"),
                    m("souther.compiler.check.Scoping$OfTheUniverse", "universe"), m("souther.compiler.query.CompilationUniverse", "db")),
                    CAPABILITY), BOTH_EVERYWHERE,
                    "Scoping.Scoped carries a way of asking the modules around this one a further "
                            + "question, and it holds this store to ask with. Where a scope has "
                            + "been taken apart already, that is the half of the assembly nobody "
                            + "has yet — it belongs inside the compute that asks"),
            new Known(new Identity(at(Q + "Front$Path", "souther.compiler.meta.ModulePath$$Lambda",
                    m(ANSWER, "value")), CAPABILITY),
                    // A function is not compared, so two of them never come apart under a walk that
                    // holds one against another; only the walk that asks each object what it is
                    // meets this.
                    ONLY_WALKED,
                    "a module path resolves a module by running something, and a function never "
                            + "equals the same function computed again"),
            new Known(new Identity(at(Q + "Front$Library", "souther.compiler.stdlib.Stdlib",
                    m(ANSWER, "value")), MISSING_EQUALITY),
                    ONLY_WALKED,
                    "a value, and here for a reason the others are not: one is built per process "
                            + "and every answer of a compilation holds that one, so identity is the "
                            + "answer structural equality would give. Writing that equality out "
                            + "would walk every declaration the library has on every comparison, "
                            + "and writing \"any library equals any other\" would be true only "
                            + "while there is one of them"),
            new Known(new Identity(at(Q + "Bodies$Expanding", "souther.compiler.stdlib.Stdlib",
                    m(ANSWER, "value"), m("souther.compiler.query.Bodies$Expanding$Of", "table"), m("souther.compiler.check.HelperTable", "stdlib")),
                    MISSING_EQUALITY), ONLY_WALKED,
                    "the same library, reached through the table an expansion reads. One thing to "
                            + "fix and two places it is held"),
            narrowedEnd(Q + "Adequacy$Inputs", walked(Scenario.VALID_CORPUS),
                    m(ANSWER, "value"), VALUE,
                    m("souther.compiler.inputs.InputDomain", "byPath"), VALUE,
                    m("souther.compiler.inputs.ReadPosition", "narrowedEnds"),
                    m("souther.compiler.check.NarrowedBounds$Reading", "lower")),
            narrowedEnd(Q + "Adequacy$Inputs", walked(Scenario.VALID_CORPUS),
                    m(ANSWER, "value"), VALUE,
                    m("souther.compiler.inputs.InputDomain", "positions"), ELEMENT,
                    m("souther.compiler.inputs.ReadPosition", "narrowedEnds"),
                    m("souther.compiler.check.NarrowedBounds$Reading", "lower")),
            // The partition's own copy. An axis carries what the reading left the position rather
            // than the names it came to, so that a border can ask whether they are about the end it
            // has — and the walk that asks each object what it is meets the end on the way.
            narrowedEnd(Q + "Adequacy$Divided", walked(Scenario.VALID_CORPUS),
                    m(ANSWER, "value"),
                    m("souther.compiler.partition.Partitions$Partitioning", "axes"), ELEMENT,
                    m("souther.compiler.partition.Axis", "narrowed"),
                    m("souther.compiler.check.NarrowedBounds$Reading", "lower")),
            new Known(new Identity(at("*", "souther.compiler.diag.Diagnostic",
                    m(ANSWER, "reports"), ELEMENT, m("souther.compiler.query.Report", "diagnostic")),
                    MISSING_EQUALITY),
                    Set.of(walked(Scenario.A_MODULE_SPOKEN_ABOUT),
                            compared(Scenario.A_MODULE_SPOKEN_ABOUT)),
                    "a report says what this compile found, and two compiles that found the same "
                            + "thing found the same thing — so what it wants is equality over what "
                            + "it says. Reached because an answer is its value and its reports "
                            + "together, which is what the store compares to stop work, and named "
                            + "without a question because the reports are the half every answer "
                            + "has: which question happens to have said anything is the scenario's "
                            + "and not this defect's"));

    /**
     * Where a walk cannot say whose denial a denial is, and why that is known.
     *
     * <p>Beside the places rather than among them, because it is not one. A thing that wrote its own
     * equality answers alike whether that equality is its parts' or its address, for as long as a
     * part of it is denying — so where one of these stands above something already written down, it
     * is what that thing costs and it goes when that thing goes.
     *
     * <p>Held to exactly, like everything else here. One arriving that stands above nothing is a
     * walk that has stopped being able to attribute something it used to.
     */
    static Set<String> cannotBeTold() {
        return Set.of(
                // Above `Names$ModuleScope`'s store, which is the line below it. `Resolve.Values`
                // wrote its own equality and is not a record, so there is no twin of it to build
                // and no way to ask what its equality is over while the store under it denies.
                "WHOSE_DENIAL_THIS_IS_CANNOT_BE_TOLD .Answer#value.Scoped#values"
                        + " in A_MODULE_SPOKEN_ABOUT",
                "WHOSE_DENIAL_THIS_IS_CANNOT_BE_TOLD .Answer#value.Scoped#values"
                        + " in VALID_CORPUS");
    }

    /** Every place written down here, whichever detector or scenario meets it. */
    static Set<Locus.Place> places() {
        Set<Locus.Place> out = new java.util.LinkedHashSet<>();
        KNOWN.forEach(each -> out.add(each.identity().place()));
        return out;
    }

    /** And who is expected to meet each of them. */
    static Map<Locus.Place, Set<String>> observations() {
        Map<Locus.Place, Set<String>> out = new LinkedHashMap<>();
        KNOWN.forEach(each -> {
            Set<String> seen = new java.util.TreeSet<>();
            each.seenBy().forEach(one -> seen.add(one.toString()));
            out.put(each.identity().place(), seen);
        });
        return out;
    }

    /** What each place is, for a reader of a failure. */
    static Map<Locus.Place, String> reasons() {
        Map<Locus.Place, String> out = new LinkedHashMap<>();
        KNOWN.forEach(each -> out.put(each.identity().place(),
                said(each.identity().meaning()) + ": " + each.reason()));
        return out;
    }

    private AnswerClosure() {
    }
}
