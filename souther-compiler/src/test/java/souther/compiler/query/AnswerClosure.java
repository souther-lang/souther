package souther.compiler.query;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

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
 * <p><b>Two axes.</b> {@link Nature} says whether the thing is something that says what it is or
 * something that does something; {@link Cause} says what is wrong with it as it stands. One word for
 * both would run them together, and they do not move together: a thing can be a value and want an
 * equality, or a value and have one that is an address, and those want different work. The remedy
 * follows from the pair — a value is finished where it is, and everything else leaves the answer.
 *
 * <p><b>Where it was seen is not what it is.</b> A finding is one finding however many detectors and
 * however many scenarios meet it, so the detector and the scenario are provenance beside the entry
 * rather than part of what it names. Held inside the identity, one thing seen twice would read as
 * two things — the same mistake as keying by class, from the other side.
 */
final class AnswerClosure {

    /** Which of the two ways out a thing takes. */
    enum Nature {
        /** Something that says what it is. Such a thing becomes comparable by what it says. */
        VALUE,
        /** Something that does something, or that carries something that does. Such a thing is
         *  built where it is used and never answered with. */
        NON_VALUE,
        /** Which of the two it is has not been read. The absence of a reading and not a third kind
         *  of thing, so it stands with {@link Cause#UNCLASSIFIED} and with nothing else. */
        NOT_READ
    }

    /** What is wrong with it as it stands. */
    enum Cause {
        /** It says what it is and defines no equality over that. */
        MISSING_VALUE_EQUALITY,
        /**
         * It has an equality and that equality is an address — its own, or its members'.
         *
         * <p>Its own word beside the one above because the work is different. Something with no
         * equality wants one written; something whose equality is an address has one already and it
         * answers the wrong question, so what it wants is to be held in something that means what it
         * says. Filed under the first, the second sends whoever picks it up to add a method beside
         * one that is already there.
         */
        IDENTITY_SEMANTICS,
        /** It is a way of asking something rather than an answer, so it is one object per store
         *  whatever it is compared with. */
        CAPABILITY,
        /** Nobody has read which of the two it is, and reading it is the fix. */
        UNCLASSIFIED
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
     * @param question the answer it is under, by the name of the key that asks it
     * @param at where in that answer it sits, as the steps of the answer's own shape
     * @param offender the class of the thing, or the array type
     */
    record Identity(Locus.Place place, Nature nature, Cause cause) {

        /**
         * The two axes say one thing between them or neither says anything.
         *
         * <p>A reading that got as far as the kind of thing and no further is not a state: what says
         * a thing is a value is the same reading that says what is wrong with it, so a line claiming
         * one without the other is a line nobody could act on.
         */
        Identity {
            if (nature == Nature.NOT_READ ^ cause == Cause.UNCLASSIFIED) {
                throw new IllegalArgumentException(
                        "what a thing is and what is wrong with it are read together: "
                                + place + " is " + nature + "/" + cause);
            }
        }
    }

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

    private static Locus.Step m(String owner, String name) {
        return new Locus.Step.Member(owner, name);
    }

    private static final Locus.Step ELEMENT = new Locus.Step.Element();
    private static final Locus.Step VALUE = new Locus.Step.MapValue();

    private static Known bytes(String question, Locus.Step... steps) {
        return new Known(new Identity(at(question, "byte[]", steps), Nature.VALUE,
                Cause.MISSING_VALUE_EQUALITY), BOTH_EVERYWHERE, CLASS_BYTES);
    }

    private static final String Q = "souther.compiler.query.";

    private static final List<Known> KNOWN = List.of(
            bytes(Q + "Output$All", m("Answer", "value"), VALUE),
            bytes(Q + "Output$Classes", m("Answer", "value"), VALUE),
            bytes(Q + "Output$Evaluated", m("Answer", "value"),
                    m("EvaluationArtifact", "classes"), VALUE),
            bytes(Q + "Output$EvaluationLinked", m("Answer", "value"),
                    m("EvaluationArtifact", "classes"), VALUE),
            // The one of the five a module on its own does not reach: nothing is linked against
            // where there is nothing to link against.
            new Known(new Identity(at(Q + "Output$Linked", "byte[]", m("Answer", "value"), VALUE),
                    Nature.VALUE, Cause.MISSING_VALUE_EQUALITY),
                    Set.of(walked(Scenario.VALID_CORPUS), compared(Scenario.VALID_CORPUS)),
                    CLASS_BYTES),
            new Known(new Identity(at(Q + "Names$ModuleScope", Q + "Db",
                    m("Answer", "value"), m("Scoped", "values"), m("Values", "elsewhere"),
                    m("OfTheUniverse", "universe"), m("CompilationUniverse", "db")),
                    Nature.NON_VALUE, Cause.CAPABILITY), BOTH_EVERYWHERE,
                    "Scoping.Scoped carries a way of asking the modules around this one a further "
                            + "question, and it holds this store to ask with. Where a scope has "
                            + "been taken apart already, that is the half of the assembly nobody "
                            + "has yet — it belongs inside the compute that asks"),
            new Known(new Identity(at(Q + "Front$Path", "souther.compiler.meta.ModulePath$$Lambda",
                    m("Answer", "value")), Nature.NON_VALUE, Cause.CAPABILITY),
                    // A function is not compared, so two of them never come apart under a walk that
                    // holds one against another; only the walk that asks each object what it is
                    // meets this.
                    ONLY_WALKED,
                    "a module path resolves a module by running something, and a function never "
                            + "equals the same function computed again"),
            new Known(new Identity(at(Q + "Front$Library", "souther.compiler.stdlib.Stdlib",
                    m("Answer", "value")), Nature.VALUE, Cause.MISSING_VALUE_EQUALITY),
                    ONLY_WALKED,
                    "a value, and here for a reason the others are not: one is built per process "
                            + "and every answer of a compilation holds that one, so identity is the "
                            + "answer structural equality would give. Writing that equality out "
                            + "would walk every declaration the library has on every comparison, "
                            + "and writing \"any library equals any other\" would be true only "
                            + "while there is one of them"),
            new Known(new Identity(at(Q + "Bodies$Expanding", "souther.compiler.stdlib.Stdlib",
                    m("Answer", "value"), m("Of", "table"), m("HelperTable", "stdlib")),
                    Nature.VALUE, Cause.MISSING_VALUE_EQUALITY), ONLY_WALKED,
                    "the same library, reached through the table an expansion reads. One thing to "
                            + "fix and two places it is held"),
            new Known(new Identity(at(Q + "Adequacy$Inputs", "souther.compiler.inputs.InputDomain",
                    m("Answer", "value"), VALUE), Nature.NOT_READ, Cause.UNCLASSIFIED),
                    BOTH_EVERYWHERE,
                    "whether it is something that says what it is or something that does something "
                            + "has to be read before it is either, so the fix is to read it"),
            new Known(new Identity(at(Q + "Bodies$Checked", Q + "Bodies$Elaborated",
                    m("Answer", "value")), Nature.NOT_READ, Cause.UNCLASSIFIED), BOTH_EVERYWHERE,
                    "as above"),
            new Known(new Identity(at("*", "souther.compiler.diag.Diagnostic",
                    m("Answer", "reports"), ELEMENT, m("Report", "diagnostic")),
                    Nature.VALUE, Cause.MISSING_VALUE_EQUALITY),
                    Set.of(walked(Scenario.A_MODULE_SPOKEN_ABOUT),
                            compared(Scenario.A_MODULE_SPOKEN_ABOUT)),
                    "a report says what this compile found, and two compiles that found the same "
                            + "thing found the same thing — so what it wants is equality over what "
                            + "it says. Reached because an answer is its value and its reports "
                            + "together, which is what the store compares to stop work, and named "
                            + "without a question because the reports are the half every answer "
                            + "has: which question happens to have said anything is the scenario's "
                            + "and not this defect's"));

    /** Every place written down here, whichever detector or scenario meets it. */
    static Set<Locus.Place> places() {
        Set<Locus.Place> out = new java.util.TreeSet<>();
        KNOWN.forEach(each -> out.add(each.identity().place()));
        return out;
    }

    /** And who is expected to meet each of them. */
    static Map<Locus.Place, Set<String>> observations() {
        Map<Locus.Place, Set<String>> out = new TreeMap<>();
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
                each.identity().nature() + "/" + each.identity().cause() + ": "
                        + each.reason()));
        return out;
    }

    private AnswerClosure() {
    }
}
