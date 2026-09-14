package souther.compiler.query;

import org.junit.jupiter.api.Test;

class WaysProbeTest {
    private static final String MODEL = """
            module example.equalanswers

            data Safe
            data Risky
            data Mode = Safe | Risky
            data On
            data Off
            data Flag = On | Off
            data X
            data Y
            data Z
            data Answer = X | Y | Z

            let choose (f: Flag, a: Answer, b: Answer): Answer = match f with
                | On -> a
                | Off -> b

            behavior decide : (mode: Mode, flag: Flag) -> Answer

            let decide (mode, flag) =
                match mode with
                    | Safe  -> choose(flag, X, X)
                    | Risky -> choose(flag, Y, Z)

            example decide
                | "safe on"   : (Safe, On)   -> X
            """;

    @Test
    void show() {
        var compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        var met = compilation.db().ask(new Adequacy.Meets("example.equalanswers")).value();
        var read = met.get("decide");
        System.out.println("INTERACTIONS " + read.interactions().size());
        var subject = Adequacy.subjectOf(compilation.db(), "example.equalanswers", "decide");
        System.out.println("AXES " + subject.axes().axes().stream().map(a -> a.id().toString()).toList());
        System.out.println("DECIDED " + souther.compiler.partition.PairFallbackPositions.of(
                read, subject.axes().axes()));
        read.arms().forEach((probe, access) ->
                System.out.println("ARM " + probe + " -> " + access.getClass().getSimpleName()
                        + (access instanceof souther.compiler.reading.PathAccess.Ways w
                                ? " ways " + w.ways().size() + " " + w.ways().stream()
                                        .map(x -> x.decisions().stream().map(d -> d.constrains().toString()).toList())
                                        .toList()
                                : "")));
    }
}
