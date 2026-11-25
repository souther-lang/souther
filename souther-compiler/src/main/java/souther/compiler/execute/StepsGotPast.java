package souther.compiler.execute;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The steps that may end a run that a run got past, each where it is written, and the calls it was
 * inside when it ended, recorded by the code as it goes.
 *
 * <p>Got past and not got to. A step is recorded once working it out answered, after what it is made
 * of was worked out and it was itself; a run that stopped at it got to it as well, and that is said
 * by where it stopped ({@link RunStop}). So a run that stopped working out what a step is made of
 * is not recorded as getting to the step, which it never did: {@code (p + 1) / q} stopping at the
 * sum never got to the quotient.
 *
 * <p>A call is recorded entered once its arguments are worked out, and left once it answers. A run
 * that ended inside one is left inside it, so what is held when the run ends is the calls it ended
 * in, the one written in the body the run began in first: a step of another declaration's body is
 * one a finding of the caller says nothing of, and the call is the step it names instead.
 *
 * <p>The compiler's and not the runtime's, for the reason {@link souther.compiler.coverage.Probe}
 * is: a class generated to say where each step that may end a run is written calls here, and the
 * loader that runs one ends at the compiler's own. Code that ships is generated without the calls.
 *
 * <p>Per thread because a run is per thread. A step passed with nothing recording is a call from
 * code nobody is watching, and dropping it is right.
 */
public final class StepsGotPast {

    /** What one run got past, and the calls it ended inside, the outermost first. */
    public record Account(Set<RunStop.Site> gotPast, List<RunStop.Site> inside) {

        public Account {
            gotPast = Set.copyOf(gotPast);
            inside = List.copyOf(inside);
        }
    }

    /** What one thread is building up while a run goes. */
    private record Recording(Set<RunStop.Site> gotPast, List<RunStop.Site> inside) {}

    private static final ThreadLocal<Recording> RECORDING = new ThreadLocal<>();

    /** Called by generated code where a step that may end a run answered. Public and static
     *  because that is what an {@code invokestatic} from a generated class needs. */
    public static void passed(String module, int line, int column) {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.gotPast().add(new RunStop.Site(module, line, column));
        }
    }

    /** Called by generated code where a call written there is entered, its arguments worked
     *  out. */
    public static void entering(String module, int line, int column) {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.inside().add(new RunStop.Site(module, line, column));
        }
    }

    /** Called by generated code where the call last entered answered. */
    public static void left() {
        Recording recording = RECORDING.get();
        if (recording != null) {
            recording.inside().removeLast();
        }
    }

    /** Starts recording on this thread. */
    public static void begin() {
        RECORDING.set(new Recording(new LinkedHashSet<>(), new ArrayList<>()));
    }

    /**
     * What this thread got past so far and the calls it is inside, and stops recording. Refused
     * where nothing was recording: what a caller has then is no account of a run rather than a run
     * that got past nothing.
     */
    public static Account end() {
        Recording recording = RECORDING.get();
        RECORDING.remove();
        if (recording == null) {
            throw new IllegalStateException("nothing is recording on this thread, so there is no"
                    + " run to say the steps of");
        }
        return new Account(recording.gotPast(), recording.inside());
    }

    private StepsGotPast() {}
}
