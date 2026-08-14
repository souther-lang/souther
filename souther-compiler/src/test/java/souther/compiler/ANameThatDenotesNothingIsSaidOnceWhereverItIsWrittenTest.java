package souther.compiler;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A type name that denotes nothing costs one diagnostic, wherever a type may be written (issue
 * #672).
 *
 * <p>{@code CascadeStopsAtTheCauseTest} holds this for what a body does with a value whose type
 * could not be worked out. This holds it for the name itself, in every position the specification
 * says a type is written in ({@code a-type-is-written-in-a-type-position}), written both on its own
 * and as one member of a union — the second because a union's members are read by a rule of their
 * own, which is where the cascade this was written for came from.
 *
 * <p>The name is reported and what was written takes the type that absorbs, which is what lets the
 * rest of the module still be checked. What must not follow is a second sentence read off that
 * type: that it is not a shape an arm can name, or that an output declares no cases at all. Both
 * were being said — the first in every position a union can be written in, the second where a
 * declared output is held against what is produced — and neither names anything an author can fix.
 *
 * <p>The code is asserted and not the count alone. A cell answering with one diagnostic that is no
 * longer the unresolved name has stopped asking the question, and a count reads that as the rule
 * holding.
 *
 * <p>The name is written qualified. A bare one is not this mistake: a name nothing declares, read
 * where a type goes, declares a unit data type (spec {@code [#unit-data]}), so there is nothing
 * unresolved about it and nothing to report once.
 */
class ANameThatDenotesNothingIsSaidOnceWhereverItIsWrittenTest {

    /** The module a qualified reference names. A qualified reference needs no import, so nothing
     * else is in the source and no unused-import warning is in the answer. */
    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int
            """;

    /** How the one mistake is spelled, beside the spelling that names something — which is what
     * says whether the position reads the form at all. */
    private record Spelling(String name, String denotesNothing, String denotesSomething) {}

    private static final List<Spelling> SPELLINGS = List.of(
            new Spelling("on its own", "up.Nope", "up.Amount"),
            new Spelling("as a union member", "A | up.Nope", "A | up.Amount"));

    /** Something to write where a position needs a value beside the type. It is not of the type
     * written above it, and does not have to be: what a position says about a value it was given is
     * that position's own question, asked by the control as much as by the probe. It builds what
     * the position that takes a value is allowed to build, so that the source stands for a reason
     * of its own rather than for the name being read. */
    private static final String VALUE = "A { a = 1 }";

    /**
     * The cells where the form cannot be written at all, so there is no name in them to report on.
     * Read rather than re-fitted: an entry leaving this list is a position that has come to admit a
     * union, and an entry arriving is one that has stopped.
     */
    private static final List<String> NOT_WRITABLE = List.of(
            "data field as a union member",
            "newtype base as a union member",
            "type argument as a union member",
            "tuple member as a union member");

    private static List<Diagnostic> diagnose(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("up.sou", UP);
        byId.put("demo.sou", source);
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()))
                .getOrDefault("demo.sou", List.of());
    }

    /** Whether the reading stopped at the form, which is an answer about no name at all. */
    private static boolean refusedTheForm(List<Diagnostic> found) {
        return found.stream().anyMatch(d -> d.said() instanceof ParseMessage);
    }

    private static String shown(List<Diagnostic> found) {
        List<String> out = new ArrayList<>();
        for (Diagnostic d : found) {
            out.add(d.code() + " " + d.values());
        }
        return out.toString();
    }

    @Test
    void theNameIsReportedAndNothingIsReadOffTheTypeItLeftBehind() {
        List<String> notWritable = new ArrayList<>();
        List<String> answered = new ArrayList<>();
        for (TypePositions.Position position : TypePositions.ALL) {
            for (Spelling spelling : SPELLINGS) {
                String cell = position.name() + " " + spelling.name();
                if (refusedTheForm(diagnose(position.of(spelling.denotesSomething(), VALUE)))) {
                    notWritable.add(cell);
                    continue;
                }
                List<Diagnostic> found =
                        diagnose(position.of(spelling.denotesNothing(), VALUE));
                if (found.size() != 1 || !"E1506".equals(found.get(0).code())) {
                    answered.add(cell + ": " + shown(found));
                }
            }
        }

        assertEquals(NOT_WRITABLE, notWritable,
                "which positions cannot be written a union; read the change rather than re-fitting");
        assertEquals(List.of(), answered,
                "the name that denotes nothing, and nothing read off the type it left behind");
    }

    /**
     * A member no arm can name is still reported when a member beside it denotes nothing.
     *
     * <p>The two are different mistakes and the author owns both: the list is a member they wrote
     * and can rewrite, and withholding it because something else in the same union went unresolved
     * would cost them a build to learn it. What is withheld is only what is read off the type the
     * unresolved name left behind.
     */
    @Test
    void aMemberNoArmCanNameIsSaidBesideAMemberThatDenotesNothing() {
        List<Diagnostic> found = diagnose("""
                module demo

                data A = { a: Int }

                behavior go : (i: A) -> List<Int> | up.Nope
                    constructs A

                let go (i) = A { a = 1 }
                """);

        assertEquals(List.of("E1506", "E1613"),
                found.stream().map(Diagnostic::code).sorted().toList(),
                "the name nothing declares, and the member no arm can name: " + shown(found));
        assertEquals(List.of(), found.stream()
                        .filter(d -> d.values().containsValue("?")).map(Diagnostic::code).toList(),
                "the member named is the one written, not the type the other member left behind: "
                        + shown(found));
    }

    /**
     * A composition over a stage whose output rests on a name that denotes nothing.
     *
     * <p>Not a cell of the sweep above: what the name is written into is one stage's own output, and
     * what would read the type it left behind is the routing of the composition beside it — which
     * would say these two behaviors cannot be composed, naming what the stage answers as {@code ?}.
     * It does not, because a signature holding the type that absorbs is abandoned where it is built
     * ({@code SignatureBoundary}) and no stage signature carries one. Held here so that the
     * composition is measured rather than reasoned about.
     */
    @Test
    void aCompositionOverAStageThatAnswersNothingIsToldOnlyTheName() {
        List<Diagnostic> found = diagnose("""
                module demo

                data A = { a: Int }
                data Out = { v: Int }

                behavior s1 : (i: Out) -> up.Nope constructs A
                let s1 (i) = A { a = 1 }

                behavior s2 : (i: A) -> A constructs A
                let s2 (i) = A { a = i.a }

                behavior go = s1 >-> s2
                """);

        assertEquals(List.of("E1506"), found.stream().map(Diagnostic::code).toList(),
                "the name that denotes nothing, and nothing about composing what it left: "
                        + shown(found));
    }
}
