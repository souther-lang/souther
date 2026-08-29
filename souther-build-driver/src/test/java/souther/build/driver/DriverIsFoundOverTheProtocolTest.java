package souther.build.driver;

import souther.build.BuildProtocol;
import souther.build.SoutherBuildDriver;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.OptionalInt;
import java.util.ServiceLoader;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a build plugin does with this artifact once it has resolved it: read the protocol it states,
 * then find the driver over the interface. Neither goes through a name the plugin has to know.
 */
class DriverIsFoundOverTheProtocolTest {

    /** Held against the constant of the API actually compiled against, so the stated number cannot
     *  stay behind when the protocol moves. */
    @Test
    void theProtocolStatedIsTheOneThisWasBuiltAgainst() {
        assertEquals(OptionalInt.of(BuildProtocol.VERSION),
                BuildProtocol.declaredBy(getClass().getClassLoader()));
    }

    @Test
    void theDriverIsFoundAsAServiceOverTheInterfaceItImplements() {
        List<SoutherBuildDriver> found =
                ServiceLoader.load(SoutherBuildDriver.class, getClass().getClassLoader())
                        .stream().map(ServiceLoader.Provider::get).toList();

        assertEquals(1, found.size(), () -> String.valueOf(found));
        assertInstanceOf(CompilerBuildDriver.class, found.get(0));
    }
}
