package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * From one module, one declaration is reached one way.
 *
 * <p>Written down because something is about to be built on it. A reader holding a call and a
 * module's carried helpers has to put the two together, and it can do that by the declaration alone
 * only where a declaration does not reach that module under two names — otherwise one identity
 * would answer for two methods and the reader would take whichever it met first.
 *
 * <p>It holds because {@link ReachName#of} decides a declaration's reach from the declaring module
 * and the reading one, and reads the spelling for neither. That is a fact about that method and not
 * about the language, so it is asked of that method here — of a behavior as well as of a helper,
 * because a behavior was once answered with the spelling instead, so a qualified reference came back
 * as a bare name that is not bare.
 */
class AHelperIsReachedOneWayFromOneModuleTest {

    private static final ValueName.Helper OURS = new ValueName.Helper("app", "flatten");
    private static final ValueName.Helper THEIRS = new ValueName.Helper("lib", "flatten");
    private static final ValueName.Stdlib.Operation LIBRARY =
            ValueName.Stdlib.operation("List", "foldFrom");

    /**
     * How a helper is written does not decide how it is reached.
     *
     * <p>The spellings below are the ones a body could hold for one declaration — the bare name an
     * import brings in, and the qualified form a rewrite writes. Neither is consulted: a helper of
     * another module is reached under the module that declares it whichever arrived.
     */
    @Test
    void whatIsWrittenDoesNotDecideHowAHelperIsReached() {
        assertEquals(Set.of(new ReachName.OfModule(THEIRS)),
                reachedFrom("app", THEIRS, "flatten", "lib.flatten"),
                "another module's helper is reached under the module that declares it");
        assertEquals(Set.of(new ReachName.Own(OURS)),
                reachedFrom("app", OURS, "flatten", "app.flatten"),
                "and the module's own is reached bare");
    }

    /** And a library operation is reached under the alias the library publishes it under, which is
     *  on the denotation rather than in the spelling. */
    @Test
    void whatIsWrittenDoesNotDecideHowALibraryOperationIsReached() {
        assertEquals(Set.of(new ReachName.OfLibrary(LIBRARY)),
                reachedFrom("app", LIBRARY, "List.fold", "List.foldFrom"),
                "one operation, reached the one way the library publishes it");
    }

    /**
     * Which module is reading decides the reach name, and it is the only thing that does.
     *
     * <p>The other side of the same rule. One declaration reaches its own module bare and every
     * other module under the module that declares it, so two modules carrying a copy of one helper
     * carry it under two reach names — and the declaration those two names denote is one.
     */
    @Test
    void whichModuleIsReadingDecidesIt() {
        assertEquals(new ReachName.Own(THEIRS), ReachName.of(THEIRS, "flatten", "lib"));
        assertEquals(new ReachName.OfModule(THEIRS), ReachName.of(THEIRS, "flatten", "app"));
    }

    /**
     * A behavior is reached the same two ways, whichever spelling reached it: another module's
     * under the module that declares it, and the module's own bare — also where the reference was
     * written through its own module, since the qualifier names this module and nothing is in the
     * way of the name. What is rendered is what was written.
     */
    @Test
    void aBehaviorIsReachedTheSameTwoWays() {
        ValueName.Behavior theirs = new ValueName.Behavior("app.a", "f");
        ValueName.Behavior ours = new ValueName.Behavior("app.own", "f");

        assertEquals(new ReachName.OfModule(theirs), ReachName.of(theirs, "app.a.f", "app.own"));
        assertEquals("app.a.f", ReachName.of(theirs, "app.a.f", "app.own").rendered());
        assertEquals(new ReachName.Own(ours), ReachName.of(ours, "f", "app.own"));
        assertEquals(new ReachName.Own(ours), ReachName.of(ours, "app.own.f", "app.own"));
    }

    /** How {@code declaration} is reached from {@code self}, over every spelling a body could
     *  hold for it. */
    private static Set<ReachName> reachedFrom(String self, ValueName declaration,
                                              String... written) {
        Set<ReachName> reached = new LinkedHashSet<>();
        for (String spelling : List.of(written)) {
            reached.add(ReachName.of(declaration, spelling, self));
        }
        return reached;
    }
}
