package souther.compiler;

import souther.compiler.source.SourceId;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Located;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Pattern;

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

    /**
     * How the one mistake is spelled, beside the spelling that names something — which is what says
     * whether the position reads the form at all — and what the position is to answer.
     *
     * <p>The third carries a second mistake the author owns: a member no arm can name. It is theirs
     * to fix whatever went unresolved beside it, so it is still said, and withholding it would cost
     * them a build to learn it. What is withheld is only what is read off the type the unresolved
     * name left behind.
     */
    private record Spelling(String name, String denotesNothing, String denotesSomething,
                            List<String> answered) {}

    private static final List<Spelling> SPELLINGS = List.of(
            new Spelling("on its own", "up.Nope", "up.Amount", List.of("E1506")),
            new Spelling("as a union member", "A | up.Nope", "A | up.Amount", List.of("E1506")),
            new Spelling("as a union member beside one no arm can name",
                    "List<Int> | up.Nope", "List<Int> | up.Amount", List.of("E1506", "E1613")),
            // The same two members the other way round. What the reading finds first is not what it
            // reports, so a reading rewritten to stop at the unresolved member is caught here.
            new Spelling("as a union member before one no arm can name",
                    "up.Nope | List<Int>", "up.Amount | List<Int>", List.of("E1506", "E1613")));

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
            "data field as a union member beside one no arm can name",
            "data field as a union member before one no arm can name",
            "newtype base as a union member",
            "newtype base as a union member beside one no arm can name",
            "newtype base as a union member before one no arm can name",
            "type argument as a union member",
            "type argument as a union member beside one no arm can name",
            "type argument as a union member before one no arm can name",
            "tuple member as a union member",
            "tuple member as a union member beside one no arm can name",
            "tuple member as a union member before one no arm can name");

    private static List<Diagnostic> diagnose(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("up.sou", UP);
        byId.put("demo.sou", source);
        return Located.diagnosticsOf(Compiler.diagnoseModules(byId, Set.of()))
                .getOrDefault(new SourceId("demo.sou"), List.of());
    }

    /** Whether the reading stopped at the form, which is an answer about no name at all. */
    private static boolean refusedTheForm(List<Diagnostic> found) {
        return found.stream().anyMatch(d -> d.said() instanceof ParseMessage);
    }

    /**
     * The type that absorbs standing where a type goes: on its own, or inside a union, a
     * collection, a tuple or a function type. It is shown as {@code ?} and nothing else is.
     *
     * <p>An optional is not this. Its {@code ?} is written onto the type it is made of
     * ({@code Int?}), so it never stands where a type begins — which is why the whole value cannot
     * simply be compared against {@code ?}, and why looking for the character anywhere in it would
     * call every optional a leak.
     */
    private static final Pattern ABSORBING = Pattern.compile("(^|[<,(|]\\s*)\\?");

    private static boolean namesTheTypeThatAbsorbs(Diagnostic d) {
        return d.values().values().stream()
                .anyMatch(v -> ABSORBING.matcher(String.valueOf(v)).find());
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
        List<String> naming = new ArrayList<>();
        for (TypePositions.Position position : TypePositions.ALL) {
            for (Spelling spelling : SPELLINGS) {
                String cell = position.name() + " " + spelling.name();
                if (refusedTheForm(diagnose(position.of(spelling.denotesSomething(), VALUE)))) {
                    notWritable.add(cell);
                    continue;
                }
                List<Diagnostic> found = diagnose(position.of(spelling.denotesNothing(), VALUE));
                if (!spelling.answered().equals(found.stream().map(Diagnostic::code).sorted().toList())) {
                    answered.add(cell + ": " + shown(found));
                }
                if (found.stream().anyMatch(ANameThatDenotesNothingIsSaidOnceWhereverItIsWrittenTest::namesTheTypeThatAbsorbs)) {
                    naming.add(cell + ": " + shown(found));
                }
            }
        }

        assertEquals(NOT_WRITABLE, notWritable,
                "which positions cannot be written a union; read the change rather than re-fitting");
        // The sharper of the two first: a diagnostic naming the type that absorbs says nothing an
        // author could go looking for, whatever else is right about the answer it is part of.
        assertEquals(List.of(), naming,
                "the type a name that denotes nothing leaves behind is named in nothing");
        assertEquals(List.of(), answered,
                "the name that denotes nothing, what is wrong beside it, and nothing else");
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
