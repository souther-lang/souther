package souther.compiler.types;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How a module reaches a behavior another module declares.
 *
 * <p>A reach name says which of the shapes a reference has, and a helper already answers this:
 * the module's own is reached as it stands, and another module's under the module that declares it.
 * A behavior is reached the same two ways and was answered with the spelling instead — so a
 * qualified reference came back as a bare name that is not bare, and a reader narrowing to the
 * shapes found nothing that says a module is in the way.
 */
class ABehaviorOfAnotherModuleIsReachedUnderItTest {

    private static final ValueName.Behavior THEIRS = new ValueName.Behavior("app.a", "f");
    private static final ValueName.Behavior OURS = new ValueName.Behavior("app.own", "f");

    @Test
    void anothersIsReachedUnderTheModuleThatDeclaresIt() {
        assertEquals(new ReachName.OfModule(THEIRS),
                ReachName.of(THEIRS, "app.a.f", "app.own"));
    }

    @Test
    void andRendersAsWhatWasWritten() {
        assertEquals("app.a.f", ReachName.of(THEIRS, "app.a.f", "app.own").rendered());
    }

    @Test
    void theModulesOwnIsReachedAsItStands() {
        assertEquals(new ReachName.Own(OURS), ReachName.of(OURS, "f", "app.own"));
    }

    /** The module's own, written through its own module. The qualifier says which module, and this
     *  is that module, so nothing is in the way of the name. */
    @Test
    void andSoIsOneWrittenThroughItsOwnModule() {
        assertEquals(new ReachName.Own(OURS), ReachName.of(OURS, "app.own.f", "app.own"));
    }
}
