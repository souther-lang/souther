package souther.compiler.query;

import souther.compiler.core.Core;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.SourceConstructOrigin;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * One comparison of one model stands in two places, and the places are not what tells it apart.
 *
 * <p>The question this settles is what a program point may be named by. A comparison inside a helper
 * handed to one of the language's own operations is inside what that operation was expanded to in
 * the tree a backend emits, and inside nothing of the kind in the tree an analysis reads — so where
 * it stands is a fact about which reading is being looked at.
 *
 * <p><b>Which closes a road.</b> A reading that named a program point by the copy tree it stands in
 * would give one comparison of one model two names, and a question raised at one of them would be
 * answered at neither. What crosses the two readings is what the source wrote and what a copy was
 * made from, and where the copies ended up is not that.
 *
 * <p>Both halves are held: that the comparison is one comparison, and that where it stands is two
 * places. Either alone says nothing — the first is only interesting because the second is true, and
 * the second is only a problem because the first is.
 */
class WhereAComparisonStandsIsNotWhatTellsItFromAnotherReadingTest {

    private static final String MODULE = """
            module demo

            data Small
            data Big
            data Size = Small | Big

            let classify (n: Int) : Size = if n > 10 then Big else Small

            behavior go : (xs: List<Int>) -> List<Size>
            let go (xs) = List.map(classify, xs)
            """;

    @Test
    void oneComparisonOfTheModelIsOneComparisonInBothReadings() {
        Bodies.Elaborated checked = checked();

        assertEquals(comparisonsIn(checked.analysisBodies().get("go").core()).keySet(),
                comparisonsIn(checked.behaviorBodies().get("go")).keySet(),
                "the model writes one comparison, and both readings of the body hold it");
    }

    /** And where it stands is two places, which is what a copy tree is a fact about. */
    @Test
    void andWhereItStandsIsTwoPlaces() {
        Bodies.Elaborated checked = checked();
        Map<SourceConstructOrigin, List<BindingOwner>> analysed =
                comparisonsIn(checked.analysisBodies().get("go").core());
        Map<SourceConstructOrigin, List<BindingOwner>> emitted =
                comparisonsIn(checked.behaviorBodies().get("go"));

        SourceConstructOrigin one = analysed.keySet().iterator().next();
        assertNotEquals(analysed.get(one), emitted.get(one),
                "the same comparison of the same model, standing in two different copy trees");
    }

    /**
     * And the difference is the operation's own body, which one reading has and the other has not.
     *
     * <p>Said so that the difference above is not read as an accident of how the walk numbered
     * something. What it is is the language's own operation: expanded in one reading, standing in
     * the other, with the helper handed to it inside what it expanded to.
     */
    @Test
    void andTheDifferenceIsTheOperationsOwnBody() {
        Bodies.Elaborated checked = checked();
        Map<SourceConstructOrigin, List<BindingOwner>> emitted =
                comparisonsIn(checked.behaviorBodies().get("go"));
        Map<SourceConstructOrigin, List<BindingOwner>> analysed =
                comparisonsIn(checked.analysisBodies().get("go").core());
        SourceConstructOrigin one = analysed.keySet().iterator().next();

        assertEquals(List.of(), expandedIn(analysed.get(one), "map"),
                "the analysis reads a tree where the operation stands, so nothing is inside it");
        assertNotEquals(List.of(), expandedIn(emitted.get(one), "map"),
                "and the backend emits one where the comparison is inside what it expanded to: "
                        + emitted.get(one));
    }

    /**
     * And the walk finds an ancestry that is there.
     *
     * <p>The three above are over what {@link #comparisonsIn} returns, and a walk that read the
     * owners off nothing would hand every one of them an empty list — which two of the three would
     * be satisfied by. So the comparison is checked to stand somewhere at all, and to stand under
     * the helper it is written in.
     */
    @Test
    void andTheWalkFindsWhereItStands() {
        Bodies.Elaborated checked = checked();
        Map<SourceConstructOrigin, List<BindingOwner>> analysed =
                comparisonsIn(checked.analysisBodies().get("go").core());

        assertEquals(1, analysed.size(), "the model under test writes one comparison");
        assertNotEquals(List.of(),
                expandedIn(analysed.get(analysed.keySet().iterator().next()), "classify"),
                "and it stands inside the helper it is written in");
    }

    /** Which of {@code ancestry} are expansions of {@code helper}. */
    private static List<BindingOwner> expandedIn(List<BindingOwner> ancestry, String helper) {
        return ancestry.stream()
                .filter(each -> each instanceof BindingOwner.Expansion it
                        && it.expanded().name().equals(helper))
                .toList();
    }

    /**
     * Every comparison the source wrote in {@code body}, with what the innermost binding around it
     * belongs to and everything that owns in turn.
     *
     * <p>Read off the bindings because a comparison has none of its own: where it stands is the copy
     * it stands in, and what says which copy that is is what the names around it belong to.
     */
    private static Map<SourceConstructOrigin, List<BindingOwner>> comparisonsIn(Core body) {
        Map<SourceConstructOrigin, List<BindingOwner>> out = new LinkedHashMap<>();
        walk(body, null, out);
        return out;
    }

    private static void walk(Core e, BindingOwner within,
                             Map<SourceConstructOrigin, List<BindingOwner>> out) {
        BindingOwner here = ownerOf(e, within);
        if (e instanceof Core.Binary it && it.origin() != null && it.origin().isWritten()) {
            out.put(it.origin(), ancestryOf(here));
        }
        Core.forEachChild(e, child -> walk(child, here, out));
    }

    /** What the names bound at {@code e} belong to, or what stood before it where it binds none. */
    private static BindingOwner ownerOf(Core e, BindingOwner within) {
        return switch (e) {
            case Core.LetIn it -> it.binder().binding().owner();
            case Core.IfConstructed it -> it.binder().binding().owner();
            case Core.Block it when !it.params().isEmpty() ->
                    it.params().get(0).binding().owner();
            default -> within;
        };
    }

    /** {@code owner} and everything it is written under, innermost first. */
    private static List<BindingOwner> ancestryOf(BindingOwner owner) {
        List<BindingOwner> out = new ArrayList<>();
        BindingOwner at = owner;
        while (at != null) {
            out.add(at);
            at = switch (at) {
                case BindingOwner.Expansion it -> it.within();
                case BindingOwner.Synthesized it -> it.within();
                default -> null;
            };
        }
        return out;
    }

    private static Bodies.Elaborated checked() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test was checked");
        assertNotNull(checked.analysisBodies().get("go"),
                "and the behavior has a body for the analysis to read");
        return checked;
    }
}
