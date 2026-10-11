package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * A recursive helper that calls itself handing one parameter something else and every other
 * parameter what it was handed: a search from a node, where each call is on another node.
 *
 * <p>Which node each call is on is not said here. What a call hands the parameter is read where the
 * body is read, against where the node it was handed stands, and a reader takes the helper as a
 * search only where every call is on an element of a container the node holds — a node strictly
 * below it, so a run goes down a finite value and never comes back to a node it was on.
 *
 * @param node  the parameter the node is handed on
 * @param again every call of itself the body makes
 */
public record RecursionOverATree(int node, List<Core.Call> again) {

    public RecursionOverATree {
        again = List.copyOf(again);
    }

    /**
     * The calls {@code body}, the body of {@code self}, makes of itself — or null where it makes
     * none, or where they hand something else on more than one parameter or on different ones.
     */
    public static RecursionOverATree of(ValueName.Helper self, CalledBody body) {
        List<Core.Call> again = new ArrayList<>();
        RecursionOverAList.callsOf(body.body(), self, again);
        List<Core.Binder> parameters = body.parameters();
        int node = -1;
        for (Core.Call call : again) {
            if (call.args().size() != parameters.size()) {
                return null;
            }
            for (int at = 0; at < parameters.size(); at++) {
                if (RecursionOverAList.parameterAt(call.args().get(at), parameters) == at) {
                    continue;
                }
                if (node >= 0 && node != at) {
                    return null;
                }
                node = at;
            }
        }
        return node < 0 ? null : new RecursionOverATree(node, again);
    }
}
