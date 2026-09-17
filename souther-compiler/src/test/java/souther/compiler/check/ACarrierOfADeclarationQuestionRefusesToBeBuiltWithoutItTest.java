package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value that holds a question about the declarations refuses to be built without it.
 *
 * <p>The questions a reader asks of a declaration it did not write are separate on purpose: which
 * form it is, what it wraps, what its fields hold, what it says. A reader asks the ones it uses, so
 * which of them a value holds differs from value to value and there is no one carrier to put them
 * in — and a value that holds one has been handed it by whoever built it, which is where handing it
 * nothing goes wrong.
 *
 * <p><b>Why this is a rule and not a habit.</b> A carrier states which questions it holds in its
 * component list and refuses the ones it holds in a condition written out by hand. The two say the
 * same thing until a question is added to one of them, and what was added to the list was not added
 * to the condition: {@code CheckContext} took what each field holds as a peer of what a name wraps,
 * said so where it is declared, and went on accepting nothing for it. Every production caller filled
 * it in, so nothing failed — which is the whole of why a reading of the code is not what should be
 * establishing this.
 *
 * <p>Read off the source rather than by building each carrier with one component missing. What is
 * being held is that the condition names the component, and a carrier is reached by constructing
 * every other component it takes — which is work per carrier, and work that says nothing more.
 */
class ACarrierOfADeclarationQuestionRefusesToBeBuiltWithoutItTest {

    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * The questions, by the name a component of one is declared with.
     *
     * <p>Named here rather than found by what implements something. They are separate interfaces
     * because they are separate questions, so there is nothing they share for this to look for —
     * and a marker they all carried would be a category invented to let this be written.
     */
    private static final Set<String> QUESTIONS = Set.of(
            "PublishedDeclarations", "DeclarationKinds", "NewtypeInners", "EffectiveFieldTypes",
            "DeclarationNewtypes", "FieldBindings", "ClauseLocations", "ExpandedClauseLookup",
            "DeclarationLocations");

    /**
     * The one carrier this does not ask it of, and why.
     *
     * <p>{@code CheckContext.Same} is a context being written out of another one: it is built from
     * the components of a {@code CheckContext} that has already refused them, and there is no path
     * that hands it anything else. A condition of its own would be the same condition twice, and
     * the day they disagreed the one further from the construction would be the wrong one.
     */
    private static final String BUILT_ONLY_FROM_A_CARRIER_THAT_REFUSED_THEM = "Same";

    @Test
    void everyCarrierThatHoldsOneRefusesToBeBuiltWithoutIt() throws IOException {
        List<Path> sources = REPOSITORY.mainJavaSources();
        assertTrue(sources.size() > 100,
                () -> "the scan found only " + sources.size() + " sources, which is not the tree");

        List<String> accepted = new ArrayList<>();
        for (Path source : sources) {
            String code = Files.readString(source, StandardCharsets.UTF_8);
            for (Carrier carrier : carriersIn(code)) {
                if (carrier.name().equals(BUILT_ONLY_FROM_A_CARRIER_THAT_REFUSED_THEM)) {
                    continue;
                }
                String refuses = refusalIn(code, carrier.name());
                for (String held : carrier.questions()) {
                    if (!refuses.contains(held + " == null")) {
                        accepted.add(source.getFileName() + " :: " + carrier.name()
                                + " holds " + held + " and is built without it");
                    }
                }
            }
        }

        assertEquals(List.of(), accepted,
                "a carrier that holds a question about the declarations and accepts nothing for it"
                        + " — the component was added to what it holds and not to what it refuses");
    }

    /** A record header and which of the questions its components are. */
    private record Carrier(String name, List<String> questions) {}

    /**
     * A type as this counts it, whether it was written under its own name or its package's.
     *
     * <p>Both spellings reach the compiler and a question asked under the second is the same
     * question — so a rule that read only the first would be a rule a caller escapes by writing the
     * package out, which is how {@code Output.Inputs} came to be outside the population the first
     * time this was run.
     */
    private static String simpleName(String type) {
        int last = type.lastIndexOf('.');
        return last < 0 ? type : type.substring(last + 1);
    }

    private static final Pattern HEADER =
            Pattern.compile("\\brecord\\s+(\\w+)\\s*\\(([^)]*?)\\)", Pattern.DOTALL);

    private static List<Carrier> carriersIn(String code) {
        List<Carrier> out = new ArrayList<>();
        Matcher header = HEADER.matcher(code);
        while (header.find()) {
            List<String> held = new ArrayList<>();
            for (String component : header.group(2).split(",")) {
                String[] words = component.trim().split("\\s+");
                if (words.length >= 2 && QUESTIONS.contains(simpleName(words[words.length - 2]))) {
                    held.add(words[words.length - 1]);
                }
            }
            if (!held.isEmpty()) {
                out.add(new Carrier(header.group(1), held));
            }
        }
        return out;
    }

    /**
     * What {@code carrier}'s compact constructor refuses, as the text of it.
     *
     * <p>Empty where it has none, which is a carrier that refuses nothing and so accepts every
     * question it holds without it.
     */
    private static String refusalIn(String code, String carrier) {
        // Whatever it is declared, which is the carrier's business and not this rule's: a compact
        // constructor written `private` refuses exactly what a `public` one does, and a rule that
        // read only one spelling would call a carrier unguarded for being closed.
        Matcher body = Pattern.compile(
                        "\\n\\s*(?:public\\s+|protected\\s+|private\\s+)?" + carrier
                                + "\\s*\\{(.*?)\\n\\s*\\}",
                        Pattern.DOTALL)
                .matcher(code);
        Set<String> found = new LinkedHashSet<>();
        while (body.find()) {
            found.add(body.group(1));
        }
        return String.join("\n", found);
    }
}
