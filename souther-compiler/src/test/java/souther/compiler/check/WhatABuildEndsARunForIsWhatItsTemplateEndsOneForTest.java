package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ReachName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Working a build of a value out works its template out, which is in no tree the build stands in:
 * read without the templates, what a build ends a run for is not known, and read with them, it is
 * what the template ends one for, the same wherever the value is built.
 */
class WhatABuildEndsARunForIsWhatItsTemplateEndsOneForTest {

    private static final String MODEL = """
            module demo

            data Count = Int
                invariant value >= 0
            let fine: Int = 3
            let past: Int = Int.abs(9223372036854775807) + 1
            let pastToo: Int = {
                let p = past
                p
            }

            behavior b : (q: Int) -> Count
                constructs Count
            let b (q) = {
                let x = fine
                let y = past
                let z = pastToo
                Count(Int.abs(q + x + y + z))
            }
            """;

    private record Read(AnalysisBody analysis, List<Core.MaterialisedValue> builds) {

        Core.MaterialisedValue of(String value) {
            return builds.stream().filter(one -> nameOf(one).equals(value)).findFirst()
                    .orElseThrow(() -> new AssertionError("no build of " + value + " among "
                            + builds.stream().map(one -> one.value().toString()).toList()));
        }

        List<Core.MaterialisedValue> allOf(String value) {
            return builds.stream().filter(one -> nameOf(one).equals(value)).toList();
        }
    }

    private static Read read() {
        Compilation compilation = ACompiledModel.answered(MODEL);
        AnalysisBody analysis = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().getFirst())).value()
                .analysisBodies().get("b");
        List<Core.MaterialisedValue> builds = new ArrayList<>();
        collect(analysis.core(), builds);
        analysis.templatesAfterTheirBuilders().forEach(template -> collect(template, builds));
        return new Read(analysis, builds);
    }

    private static void collect(Core e, List<Core.MaterialisedValue> into) {
        if (Core.withoutStanding(e) instanceof Core.MaterialisedValue build) {
            into.add(build);
        }
        Core.forEachChild(e, child -> collect(child, into));
    }

    private static String nameOf(Core.MaterialisedValue build) {
        return switch (build.value()) {
            case ReachName.Own(var denotes) -> denotes.name();
            case ReachName.OfModule(var denotes) -> denotes.name();
            default -> "";
        };
    }

    @Test
    void aBuildReadWithoutItsTemplateIsNotKnownToEndNoRun() {
        Read read = read();
        Map<String, WhatARunMayEndFor.Endings> each = new LinkedHashMap<>();
        for (String value : List.of("fine", "past", "pastToo")) {
            each.put(value, WhatARunMayEndFor.itself(read.of(value)));
        }
        each.forEach((value, endings) ->
                assertInstanceOf(WhatARunMayEndFor.Endings.NotKnown.class, endings, value));
    }

    @Test
    void aBuildReadWithItsTemplateEndsWhatTheTemplateEnds() {
        Read read = read();
        WhatARunMayEndFor.WithDefinitions with =
                new WhatARunMayEndFor.WithDefinitions(read.analysis().templates());
        assertTrue(with.itself(read.of("fine")).endsNone(), "a template that ends no run");
        assertTrue(!with.itself(read.of("past")).endsNone(), "a template past its type");
        assertTrue(!with.itself(read.of("pastToo")).endsNone(),
                "a template building one past its type");
    }

    @Test
    void aValueIsOneAnswerWhereverItIsBuilt() {
        Read read = read();
        WhatARunMayEndFor.WithDefinitions with =
                new WhatARunMayEndFor.WithDefinitions(read.analysis().templates());
        List<Core.MaterialisedValue> pasts = read.allOf("past");
        assertEquals(2, pasts.size(), "built in the body and in another value's template");
        assertEquals(with.itself(pasts.get(0)),
                new WhatARunMayEndFor.WithDefinitions(read.analysis().templates())
                        .itself(pasts.get(1)));
    }
}
