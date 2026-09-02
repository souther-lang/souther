package souther.compiler.ast;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which forms say where a construction came from, and which may not.
 *
 * <p>A construction stands somewhere other than where it was written only after a body has been
 * spliced into a reader, and no parse decides that. So no form of the parsed tree holds one, and
 * {@link TheParsedTreeHoldsOnlyWhatTheFrontendWritesTest} says the same about forms as this says
 * about a form's parts: a component the frontend cannot vary reads as a distinction the parse draws,
 * and offers a pass below an answer to take — one that says the reader's own wherever it is asked,
 * since that is all a parse can put there.
 *
 * <p>Below, two forms hold one and the rest may not. A construction node carries its own, and a
 * recursive helper is lowered to a method rather than expanded, so the call it is left as carries
 * what would have stood behind it. A third holder would be a mark someone writes and the permission
 * check does not read — which is what {@code ValueName.OfType} was — or a second place the same
 * question is answered, and the check that reads these forms would not know to look at it.
 *
 * <p>The pair is asserted rather than assumed, because the check over the compiled classes takes the
 * forms it watches from this same walk. Both read a component's own type: a form whose component
 * were a form that holds one would hold one at a remove, and neither says it may not.
 */
class TheParsedTreeDoesNotSayWhereAConstructionCameFromTest {

    @Test
    void noFormOfTheParsedTreeHoldsWhereAConstructionCameFrom() {
        assertEquals(List.of(), holdersIn(Ast.class),
                "a parse answers `own` and nothing else here, so the component is a question the"
                        + " parsed tree cannot answer. Where a construction came from is settled"
                        + " below, on the node the inliner carries");
    }

    @Test
    void belowItISaidByTheConstructionAndByTheCallAHelperIsLeftAs() {
        assertEquals(List.of("Apply.origin", "NewData.origin"), holdersIn(Hir.class),
                "these are the forms a pass can be handed a construction through, and the ones the"
                        + " permission check asks. A form added here is a place the same question"
                        + " is answered that nothing reads");
    }

    /**
     * An origin answers nothing on its own, so a reader has to ask the form that holds it.
     *
     * <p>Read as "there is no public protocol here" rather than as a list of members that may not
     * be declared: a member on this type is public whatever it is called, because that is what an
     * interface member is. One would be a second place to ask what a construction's origin means —
     * reached through whatever a pass happens to hold rather than through the form that knows what
     * it is — and a second place to change one.
     *
     * <p>The arms are held to the same thing from the other side. Sealed, so no one else is one;
     * declared here, so no one else can name one; and not public, because a record's canonical
     * constructor is as accessible as the record, and a public arm is a public way to mint an
     * origin.
     */
    @Test
    void andAnOriginIsAskedThroughTheFormRatherThanAnsweringForItself() {
        assertEquals(List.of(), Arrays.stream(ConstructionOrigin.class.getDeclaredMethods())
                        .map(Method::getName).sorted().toList(),
                "a member here is a public one, and the questions belong to the package that holds"
                        + " the forms");
        assertTrue(ConstructionOrigin.class.isSealed(), "an origin is one of the arms below");
        for (Class<?> arm : ConstructionOrigin.class.getPermittedSubclasses()) {
            assertEquals(ConstructionOrigin.class.getPackageName(), arm.getPackageName(),
                    arm + " is named where an origin may be made");
            assertFalse(Modifier.isPublic(arm.getModifiers()),
                    arm + " would be a public way to mint one");
        }
    }

    /** The control: the walk reaches the forms and reads their parts. */
    @Test
    void andTheCheckReadsTheFormsAndTheirParts() {
        assertTrue(forms(Ast.class).contains(Ast.NewData.class), "the walk reaches a construction");
        assertTrue(Arrays.stream(Ast.NewData.class.getRecordComponents())
                        .anyMatch(part -> part.getName().equals("typeName")),
                "and reads what it holds");
    }

    /** Every component of {@code tree}'s forms that says where a construction came from. */
    static List<String> holdersIn(Class<?> tree) {
        List<String> holders = new ArrayList<>();
        for (Class<?> form : forms(tree)) {
            for (RecordComponent part : form.getRecordComponents()) {
                if (ConstructionOrigin.class.isAssignableFrom(part.getType())) {
                    holders.add(form.getSimpleName() + "." + part.getName());
                }
            }
        }
        return holders.stream().sorted().toList();
    }

    /** The forms of {@code tree}: its nest members that have components. */
    private static List<Class<?>> forms(Class<?> tree) {
        return Arrays.stream(tree.getNestMembers()).filter(Class::isRecord).toList();
    }
}
