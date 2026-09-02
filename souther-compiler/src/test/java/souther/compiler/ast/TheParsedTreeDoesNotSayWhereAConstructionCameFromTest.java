package souther.compiler.ast;

import souther.compiler.types.ConstructionOrigin;

import org.junit.jupiter.api.Test;

import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction stands somewhere other than where it was written only after a body has been
 * spliced into a reader, and no parse decides that. So no form of the parsed tree holds where a
 * construction came from.
 *
 * <p>{@link TheParsedTreeHoldsOnlyWhatTheFrontendWritesTest} says the same about forms; this says it
 * about a form's parts. A component the frontend cannot vary reads as a distinction the parse
 * draws, and offers a pass below a value to take an answer from — one that says the reader's own
 * wherever it is asked, since that is all a parse can put there.
 *
 * <p>What is measured is the component's own type. A form holding another form that holds one would
 * pass here and is what the check beside this one is about: the parsed tree holds no form of the
 * tree below.
 */
class TheParsedTreeDoesNotSayWhereAConstructionCameFromTest {

    @Test
    void noFormOfTheParsedTreeHoldsWhereAConstructionCameFrom() {
        List<String> saying = new ArrayList<>();
        for (Class<?> form : forms()) {
            for (RecordComponent part : form.getRecordComponents()) {
                if (ConstructionOrigin.class.isAssignableFrom(part.getType())) {
                    saying.add(form.getSimpleName() + "." + part.getName());
                }
            }
        }

        assertEquals(List.of(), saying.stream().sorted().toList(),
                "a parse answers `own` and nothing else here, so the component is a question the"
                        + " parsed tree cannot answer. Where a construction came from is settled"
                        + " below, on the node the inliner carries");
    }

    /** The control: the walk reaches the forms this is about, and reads their parts. */
    @Test
    void andTheCheckReadsTheFormsAndTheirParts() {
        List<Class<?>> forms = forms();

        assertTrue(forms.contains(Ast.NewData.class), "the walk reaches a construction");
        assertTrue(Arrays.stream(Ast.NewData.class.getRecordComponents())
                        .anyMatch(part -> part.getName().equals("typeName")),
                "and reads what it holds");
    }

    /** The forms of the parsed tree: the nest members of {@link Ast} that have components. */
    private static List<Class<?>> forms() {
        return Arrays.stream(Ast.class.getNestMembers()).filter(Class::isRecord).toList();
    }
}
