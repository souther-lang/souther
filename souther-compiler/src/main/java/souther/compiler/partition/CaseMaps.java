package souther.compiler.partition;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.IntPredicate;

import net.unit8.notation199x.CaseConversion;
import souther.compiler.evaluate.BoundUnderEvaluation;
import souther.compiler.regex.CodeMap;
import souther.compiler.semantics.CaseMapping;

/**
 * A case conversion as the map on code points it is exactly one for ({@link CodeMap}), worked out
 * from the run time's own conversion the first time a conversion is asked of, and kept for the
 * rest: the map is a fact of the language and not of the model being read.
 */
final class CaseMaps {

    private static final Map<CaseMapping, CodeMap> MADE = new ConcurrentHashMap<>();

    private CaseMaps() {
    }

    /**
     * The map {@code mapping} is on the code points it is exactly one for.
     *
     * <p>What it leaves be is what its outermost conversion leaves be. Converting what a
     * conversion answered changes nothing more only for the one conversion done again; of
     * {@code lowercase(uppercase(s))} that is not so ({@code ß} is what it answers of {@code ẞ},
     * and it answers {@code ss} of that), but every code point of its answer is one of the outer
     * conversion's.
     */
    static CodeMap of(CaseMapping mapping) {
        CodeMap had = MADE.get(mapping);
        if (had == null) {
            had = CodeMap.of(text -> BoundUnderEvaluation.mapped(mapping, text),
                    leftAloneEverywhere(mapping));
            CaseMapping outermost = switch (mapping) {
                case CaseMapping.None it -> it;
                case CaseMapping.Lowercase _ -> CaseMapping.LOWERCASE;
                case CaseMapping.Uppercase _ -> CaseMapping.UPPERCASE;
            };
            if (!outermost.equals(mapping) && !(mapping instanceof CaseMapping.None)) {
                had = had.leavingBe(of(outermost).leftAlone());
            }
            CodeMap raced = MADE.putIfAbsent(mapping, had);
            if (raced != null) {
                had = raced;
            }
        }
        return had;
    }

    /**
     * Whether {@code mapping} answers a code point as it is in every text, as the tables of the
     * case conversion the run time does it with say: where each conversion it is made of does.
     */
    static IntPredicate leftAloneEverywhere(CaseMapping mapping) {
        return switch (mapping) {
            case CaseMapping.None _ -> codePoint -> true;
            case CaseMapping.Lowercase(CaseMapping of) -> {
                IntPredicate inner = leftAloneEverywhere(of);
                yield codePoint -> CaseConversion.lowercaseLeavesAlone(codePoint)
                        && inner.test(codePoint);
            }
            case CaseMapping.Uppercase(CaseMapping of) -> {
                IntPredicate inner = leftAloneEverywhere(of);
                yield codePoint -> CaseConversion.uppercaseLeavesAlone(codePoint)
                        && inner.test(codePoint);
            }
        };
    }
}
