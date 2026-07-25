// 案件登録の HTTP 境界。流れは HTTP -> decode -> 応募期限の検査 -> 想定総額 -> encode / ステータス。
// 境界は data を作れない（コンストラクタは公開されていない）ので、できるのは入力を decoder に通し、
// 出力のケースを status と body に畳むことだけ。
//
// 元の Java 実装（validation-modeling の JobOfferController）は decoder を手で組み立てて同じことを
// していた。違いは decoder の出どころだけで、境界の形は同じ ── Ok なら値、Err なら Issues を 400。
package app.joboffer.web;

import example.joboffer.依頼;
import example.joboffer.掲載可;
import example.joboffer.応募期限を検査する;
import example.joboffer.期限が先すぎる;
import example.joboffer.期限切れ;
import example.joboffer.想定総額;
import example.joboffer.総額確定;
import example.joboffer.総額未定;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;

import org.springframework.http.ResponseEntity;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import tools.jackson.databind.JsonNode;

import java.time.Clock;
import java.time.LocalDate;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * {@code POST /api/job-offers}。body は依頼の JSON で、種別は判別子 {@code "type"} が持つ
 * （{@code "プロジェクト依頼"} / {@code "タスク依頼"} / {@code "コンペ依頼"}）。精算方式・予算・
 * 契約金額といった入れ子の直和も、それぞれ同じ {@code "type"} で分岐する。
 *
 * <p>読むのは {@code 依頼.jsonDecoder()} ── Jackson の {@code JsonNode} を直に読む方の decoder で、
 * 応募期限のような日付を JSON のテキストから取る。中立ツリー用の {@code decoder()} は
 * {@code LocalDate} を受け取る側なので、HTTP の入口ではこちらを使う。
 *
 * <p>ステータス: 受理 = 201 / 応募期限が範囲外 = 422 / decode 失敗 = 400。
 */
@RestController
@RequestMapping("/api/job-offers")
public final class JobOfferController {

    private final 想定総額 見積もる;
    private final 応募期限を検査する 期限を検査する;
    private final Clock clock;

    public JobOfferController(想定総額 見積もる, 応募期限を検査する 期限を検査する, Clock clock) {
        this.見積もる = 見積もる;
        this.期限を検査する = 期限を検査する;
        this.clock = clock;
    }

    @PostMapping
    public ResponseEntity<Object> create(@RequestBody JsonNode body) {
        return switch (依頼.jsonDecoder().decode(body, Path.ROOT)) {
            // decode 失敗: どのフィールドがどの規則で落ちたかを Issues が持っている。入れ子の直和で
            // 落ちても、パスは壊れた場所まで降りている（精算/予算枠/上限 など）。
            case Err<依頼>(var issues) -> ResponseEntity.badRequest().body(Map.of(
                    "error", "invalid_job_offer",
                    "issues", issues.asList().stream().map(JobOfferController::describe).toList()));

            case Ok<依頼>(var offer) -> switch (期限を検査する.apply(offer, LocalDate.now(clock))) {
                case 掲載可 _ -> ResponseEntity.status(201).body(accepted(offer));
                case 期限切れ 切れ -> ResponseEntity.unprocessableEntity().body(Map.of(
                        "error", "offer_expired", "daysPast", 切れ.超過日数()));
                case 期限が先すぎる 先 -> ResponseEntity.unprocessableEntity().body(Map.of(
                        "error", "offer_expire_date_too_far", "daysAhead", 先.残り日数()));
            };
        };
    }

    /** 受理した依頼と、その想定総額。予算未定の依頼は金額が出ないので、そのケースをそのまま返す。 */
    private Map<String, Object> accepted(依頼 offer) {
        Map<String, Object> out = new LinkedHashMap<>();
        out.put("jobOffer", 依頼.encoder().encode(offer));
        out.put("estimate", switch (見積もる.apply(offer)) {
            case 総額確定 確定 -> Map.of("decided", true, "amount", 確定.金額().value());
            case 総額未定 _ -> Map.of("decided", false);
        });
        return out;
    }

    /** 1 件の decode エラーを、壊れた場所（パス）と規則（コード）で表す。 */
    private static Map<String, Object> describe(Issue issue) {
        Map<String, Object> out = new LinkedHashMap<>();
        out.put("path", issue.path().toString());
        out.put("code", issue.code());
        out.put("message", issue.message());
        return out;
    }
}
