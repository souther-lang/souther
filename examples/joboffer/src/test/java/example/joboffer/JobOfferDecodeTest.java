package example.joboffer;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * 導出された decoder を Spring 抜きで直接見る。joboffer.sou には decoder の記述が一行も無く、
 * 制約は newtype の invariant にしか書かれていない ── ここで確かめるのは、その invariant が
 * 境界の検査として効いていることと、直和が何段入れ子になってもエラーが壊れた場所を指すこと。
 *
 * <p>元の Java 実装（validation-modeling の JobOfferJsonDecoders）は同じ制約を
 * {@code long_().min(2).max(1023)} のように decoder 側に書いていた。境界での振る舞いは同じで、
 * 書く場所が違う。
 */
class JobOfferDecodeTest {

    private final JsonMapper json = JsonMapper.builder().build();

    private Result<依頼> decode(String body) {
        JsonNode node = json.readTree(body);
        return 依頼.jsonDecoder().decode(node, Path.ROOT);
    }

    /** 読めたはずの body を読む。読めなければ Issues を添えて落とす。 */
    private 依頼 decoded(String body) {
        return switch (decode(body)) {
            case Ok<依頼>(var 依頼) -> 依頼;
            case Err<依頼>(var issues) -> throw new AssertionError("should decode: " + issues.asList());
        };
    }

    /** 読めないはずの body から、返った Issues を取り出す。 */
    private List<Issue> issuesOf(String body) {
        return switch (decode(body)) {
            case Err<依頼>(var issues) -> issues.asList();
            case Ok<依頼>(var 依頼) -> throw new AssertionError("should not decode: " + 依頼);
        };
    }

    @Test
    void 三段入れ子の直和が一度に読める() {
        依頼 offer = decoded("""
                {
                  "type": "プロジェクト依頼",
                  "タイトル": "運用支援",
                  "詳細": "週次の運用代行",
                  "応募期限": "2026-08-01",
                  "精算": {
                    "type": "固定精算",
                    "人数": 4,
                    "予算枠": { "type": "範囲予算", "下限": 30000, "上限": 80000 }
                  }
                }
                """);

        プロジェクト依頼 project = assertInstanceOf(プロジェクト依頼.class, offer);
        固定精算 fixed = assertInstanceOf(固定精算.class, project.精算());
        範囲予算 range = assertInstanceOf(範囲予算.class, fixed.予算枠());
        assertEquals(30000, range.下限().value());
        assertEquals(80000, range.上限().value());
    }

    @Test
    void 値を持たないケースはtypeタグだけで読める() {
        依頼 offer = decoded("""
                {
                  "type": "コンペ依頼",
                  "タイトル": "キャッチコピー",
                  "詳細": "新商品のコピー",
                  "応募期限": "2026-08-01",
                  "金額": { "type": "スタンダード" }
                }
                """);

        コンペ依頼 competition = assertInstanceOf(コンペ依頼.class, offer);
        assertInstanceOf(スタンダード.class, competition.金額());
    }

    @Test
    void 日付はJSONのテキストから読む() {
        依頼 offer = decoded("""
                {
                  "type": "コンペ依頼",
                  "タイトル": "キャッチコピー",
                  "詳細": "新商品のコピー",
                  "応募期限": "2026-08-01",
                  "金額": { "type": "エコノミー" }
                }
                """);

        assertEquals(java.time.LocalDate.of(2026, 8, 1),
                assertInstanceOf(コンペ依頼.class, offer).応募期限());
    }

    @Test
    void newtypeのinvariantが境界の検査になる() {
        // 作業単価は 6..999999。5 は下限割れ。
        List<Issue> issues = issuesOf("""
                {
                  "type": "タスク依頼",
                  "タイトル": "文字起こし",
                  "詳細": "音声の書き起こし",
                  "応募期限": "2026-08-01",
                  "単価": 5,
                  "件数": 500,
                  "一人あたり": { "type": "制限なし" }
                }
                """);

        assertEquals(1, issues.size(), issues.toString());
        assertTrue(issues.get(0).path().toString().contains("単価"), issues.toString());
    }

    @Test
    void 壊れたフィールドが複数あれば全部返る() {
        // タイトルが空、件数が上限超え。decoder は最初の一件で止まらない。
        List<Issue> issues = issuesOf("""
                {
                  "type": "タスク依頼",
                  "タイトル": "",
                  "詳細": "音声の書き起こし",
                  "応募期限": "2026-08-01",
                  "単価": 100,
                  "件数": 1000000,
                  "一人あたり": { "type": "制限なし" }
                }
                """);

        assertEquals(2, issues.size(), issues.toString());
        String paths = issues.stream().map(i -> i.path().toString()).toList().toString();
        assertTrue(paths.contains("タイトル"), paths);
        assertTrue(paths.contains("件数"), paths);
    }

    @Test
    void 必須フィールドの欠落も同じ経路で落ちる() {
        List<Issue> issues = issuesOf("""
                {
                  "type": "コンペ依頼",
                  "タイトル": "キャッチコピー",
                  "応募期限": "2026-08-01",
                  "金額": { "type": "プレミアム" }
                }
                """);

        assertEquals(1, issues.size(), issues.toString());
        assertTrue(issues.get(0).path().toString().contains("詳細"), issues.toString());
    }

    @Test
    void 内側の直和のタグが未知なら内側で落ちる() {
        List<Issue> issues = issuesOf("""
                {
                  "type": "プロジェクト依頼",
                  "タイトル": "運用支援",
                  "詳細": "週次の運用代行",
                  "応募期限": "2026-08-01",
                  "精算": { "type": "出来高精算", "人数": 4 }
                }
                """);

        assertTrue(issues.toString().contains("精算"), issues.toString());
    }
}
