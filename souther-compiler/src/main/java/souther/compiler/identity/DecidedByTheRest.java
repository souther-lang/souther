package souther.compiler.identity;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A field the identity around it does not read, because the fields it does read decide this one.
 *
 * <p>What a state answers with is its identity: the store compares the answer it recomputed against
 * the one it held, and a field left out of that comparison is one every reader keeps the old value
 * of with nothing anywhere saying so. So a field outside an identity has to be one that cannot
 * differ while the rest agrees.
 *
 * <p>Which way round it was settled is not what this says. A field the constructor works out from
 * the ones beside it and a field the constructor was handed and worked the others out from are both
 * one fact held twice, and neither can come apart from the rest. What is claimed is that: the rest
 * decides it.
 *
 * <p><b>Declared and not read off the shape.</b> Whether one field is decided by the others is not
 * something a reading of the class can answer, and the two fields that happen to agree everywhere a
 * test looked are the ones a reading would pass over. Said here instead, at the field, so the claim
 * is made by whoever wrote it and is where the next writer of that class will meet it.
 *
 * <p>A lazily worked-out answer says the same thing by being {@code volatile}, and a record says it
 * by having no identity written apart from its components. This is for the third way: a final field
 * settled where the state is made, beside the ones that decide it.
 *
 * <p>Its own package because the states the store compares are written in more than one, and a word
 * all of them can say belongs somewhere none of them owns.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.FIELD)
public @interface DecidedByTheRest {
}
