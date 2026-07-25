package app.joboffer;

import org.junit.jupiter.api.Test;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.core.env.Environment;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;
import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Boot を実際に起動し（RANDOM_PORT で Tomcat が上がる）、{@code POST /api/job-offers} を本物の HTTP で
 * 叩く。通る経路は Tomcat -> Jackson -> {@code 依頼.jsonDecoder()} -> 純粋な behavior -> JSON。
 * データベースは無い。
 *
 * <p>効かせているのは入れ子の直和で、依頼の種別・精算方式・予算・契約金額がそれぞれ独立に
 * {@code "type"} で分岐する。どの段で壊れても 400 になり、Issues が壊れた場所のパスを持つ。
 */
@SpringBootTest(webEnvironment = SpringBootTest.WebEnvironment.RANDOM_PORT)
class JobOfferApiTest {

    @Autowired Environment env;

    private final HttpClient http = HttpClient.newHttpClient();
    private final JsonMapper json = JsonMapper.builder().build();

    /** 応募期限は「今日から14日以内」しか受け付けないので、テストの日付は今日からの相対で作る。 */
    private static String 期限(int 日後) {
        return LocalDate.now().plusDays(日後).toString();
    }

    private HttpResponse<String> post(String body) throws Exception {
        int port = env.getRequiredProperty("local.server.port", Integer.class);
        HttpRequest req = HttpRequest.newBuilder()
                .uri(URI.create("http://localhost:" + port + "/api/job-offers"))
                .header("Content-Type", "application/json; charset=UTF-8")
                .POST(HttpRequest.BodyPublishers.ofString(body, StandardCharsets.UTF_8))
                .build();
        return http.send(req, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
    }

    @Test
    void プロジェクト依頼は精算方式まで降りて総額が出る() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "プロジェクト依頼",
                  "タイトル": "コーポレートサイトのリニューアル",
                  "詳細": "既存サイトの構成そのままでデザインを刷新する",
                  "応募期限": "%s",
                  "精算": {
                    "type": "固定精算",
                    "人数": 3,
                    "予算枠": { "type": "上限予算", "上限": 50000 }
                  }
                }
                """.formatted(期限(7)));

        assertEquals(201, res.statusCode(), res.body());
        JsonNode body = json.readTree(res.body());
        assertEquals(true, body.get("estimate").get("decided").asBoolean());
        assertEquals(150000, body.get("estimate").get("amount").asLong(), "上限 50000 × 3人");
        // encode は decode の逆向き。判別子タグも入れ子ごとに書き戻る。
        assertEquals("プロジェクト依頼", body.get("jobOffer").get("type").asString());
        assertEquals("固定精算", body.get("jobOffer").get("精算").get("type").asString());
        assertEquals("上限予算", body.get("jobOffer").get("精算").get("予算枠").get("type").asString());
    }

    @Test
    void 予算が未定なら総額は出ないが依頼としては受理される() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "プロジェクト依頼",
                  "タイトル": "ロゴ制作",
                  "詳細": "コーポレートロゴ一式",
                  "応募期限": "%s",
                  "精算": {
                    "type": "固定精算",
                    "人数": 2,
                    "予算枠": { "type": "未定予算" }
                  }
                }
                """.formatted(期限(3)));

        assertEquals(201, res.statusCode(), res.body());
        JsonNode body = json.readTree(res.body());
        assertFalse(body.get("estimate").get("decided").asBoolean(), "未定は 0 円ではなく別のケース");
        assertFalse(body.get("estimate").has("amount"));
    }

    @Test
    void 時間精算はレンジの下限で見積もる() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "プロジェクト依頼",
                  "タイトル": "運用支援",
                  "詳細": "週次の運用代行",
                  "応募期限": "%s",
                  "精算": {
                    "type": "時間精算",
                    "人数": 2,
                    "単価": { "type": "時給1500円から2000円" },
                    "稼働時間": 10,
                    "期間": { "type": "一ヶ月から三ヶ月" }
                  }
                }
                """.formatted(期限(10)));

        assertEquals(201, res.statusCode(), res.body());
        JsonNode body = json.readTree(res.body());
        assertEquals(120000, body.get("estimate").get("amount").asLong(), "1500 × 10h × 4週 × 2人");
    }

    @Test
    void タスク依頼は作業単価と件数から出る() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "タスク依頼",
                  "タイトル": "文字起こし",
                  "詳細": "会議音声の書き起こし",
                  "応募期限": "%s",
                  "単価": 100,
                  "件数": 500,
                  "一人あたり": { "type": "制限あり", "上限": 50 }
                }
                """.formatted(期限(14)));

        assertEquals(201, res.statusCode(), res.body());
        assertEquals(50000, json.readTree(res.body()).get("estimate").get("amount").asLong());
    }

    @Test
    void コンペ依頼のカスタム金額は指値がそのまま総額になる() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "コンペ依頼",
                  "タイトル": "キャッチコピー",
                  "詳細": "新商品のコピーを募集する",
                  "応募期限": "%s",
                  "金額": { "type": "カスタム金額", "指値": 330000 }
                }
                """.formatted(期限(5)));

        assertEquals(201, res.statusCode(), res.body());
        assertEquals(330000, json.readTree(res.body()).get("estimate").get("amount").asLong());
    }

    @Test
    void 入れ子の奥で規則を外れると壊れた場所のパスが返る() throws Exception {
        // 募集人数は 2..1023。1 は下限割れで、それが精算の中で起きている。
        HttpResponse<String> res = post("""
                {
                  "type": "プロジェクト依頼",
                  "タイトル": "ロゴ制作",
                  "詳細": "コーポレートロゴ一式",
                  "応募期限": "%s",
                  "精算": {
                    "type": "固定精算",
                    "人数": 1,
                    "予算枠": { "type": "上限予算", "上限": 50000 }
                  }
                }
                """.formatted(期限(7)));

        assertEquals(400, res.statusCode(), res.body());
        JsonNode issues = json.readTree(res.body()).get("issues");
        assertEquals(1, issues.size(), res.body());
        assertTrue(issues.get(0).get("path").asString().contains("人数"),
                "壊れたのは精算の中の人数: " + issues.get(0));
    }

    @Test
    void 未知の種別タグは受け付けない() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "見積依頼",
                  "タイトル": "何か",
                  "詳細": "何か",
                  "応募期限": "%s"
                }
                """.formatted(期限(7)));

        assertEquals(400, res.statusCode(), res.body());
    }

    @Test
    void 応募期限が過ぎていれば受理しない() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "コンペ依頼",
                  "タイトル": "キャッチコピー",
                  "詳細": "新商品のコピーを募集する",
                  "応募期限": "%s",
                  "金額": { "type": "ベーシック" }
                }
                """.formatted(期限(-5)));

        assertEquals(422, res.statusCode(), res.body());
        JsonNode body = json.readTree(res.body());
        assertEquals("offer_expired", body.get("error").asString());
        assertEquals(5, body.get("daysPast").asLong());
    }

    @Test
    void 応募期限が14日より先でも受理しない() throws Exception {
        HttpResponse<String> res = post("""
                {
                  "type": "コンペ依頼",
                  "タイトル": "キャッチコピー",
                  "詳細": "新商品のコピーを募集する",
                  "応募期限": "%s",
                  "金額": { "type": "ベーシック" }
                }
                """.formatted(期限(30)));

        assertEquals(422, res.statusCode(), res.body());
        JsonNode body = json.readTree(res.body());
        assertEquals("offer_expire_date_too_far", body.get("error").asString());
        assertEquals(30, body.get("daysAhead").asLong());
    }
}
