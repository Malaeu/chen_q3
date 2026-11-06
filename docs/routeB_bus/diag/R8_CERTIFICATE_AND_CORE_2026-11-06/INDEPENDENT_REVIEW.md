# Independent read-only review

Reviewer: native `/root/independent_review`, GPT-6 Astra (low), distinct from
both implementation workers and root. This is a root-observed native review,
not an external signed receipt or provider-attested mathematical admission.

Final verdict: **PASS for the stated finite computational scope. No material
actionable findings remain.**

The reviewer checked rational witness arithmetic and exact binary64 coefficient
preservation at N=500/1000/2000; the half-gradient correction and inverse-trace
bound; gamma_(8K+16) budgets including the initial constant, subnormal and decimal
allowances; upper-end threshold decisions and computed J1/J2 predicates; all
eight certificate rows; selected core values, 27 crossings and first crossing
43297; 198 J3 comparisons; and final core source/run hash consistency.
The reviewer independently recomputed J4 slopes as 0.5191977397533443 and
0.5216222853522573.

Earlier draft findings (rounding allowance, endpoint selection, hardcoded judge
statuses, N=100/200 comparisons, and shared native scratch storage) were fixed
before the final production run and final review.

Limits explicitly accepted in the report: J3 is the clarified finite identity
subjudge only; the infinite tail was not independently summed. Head and shoulder
values remain diagnostics. P4 has an empty domain; P5 is only a finite-band test.
The reviewer did not rerun complete production computations or independently
reproduce every MPFR sign. No RH claim or route promotion is made.

The final reviewer supplied these reviewed SHA-256 bindings (verified against
current bytes when this record was written):

```text
d4b8fbbd07eb7cd993e0b1ca8fd1035795553a06b8048fb9b5ca8549a2e6558f certificate.py
3e051681d3776ff5e45ff821c3ea6341aac8a4c117cb03466d8ce634fbdf9e94 certificate_native.cpp
5808c5bda736504dc3b2c5b3d47baa30f8f28383721ee8818fc1d7a672b8e42a certificate_method.md
d8e228895c89e7aa50222ddfb5cfc99d5d9328d1028467fe274230033db976ab certificate_results.csv
f8434fabad47a72038eb4f32fe7778cefb0ae33cecf506c18681851d31a38289 certificate_judges.csv
73c59a6bfba1dca4d26658d2d83be13c3e7dc4e9cb6159b082f5b501a59e2607 certificate_summary.json
9c0728bc997e0dd03e398a7ee69d97a4d6f196902a856451372f1ed96a536f92 core_scan.cpp
82d0a014833bf04ee2ba1138bb7bc2ac5e5230e7640db340656427893f3f26c1 core_judges.json
bafe5138b5d9d7fe84e2f07a2a85842221cc3e3b3c2c802952c62e8cf7d8e8f2 core_method.md
c59b12e75637f4d2227218d866574d99f701a0e8de7c7f75a1853ab4daea85aa JUDGE_ANALYSIS.md
154178b264b10ae21a4a5bb41208c0c6d8b075cc3718956639b37c987cf04e42 PREREGISTRATION.json
6380ac5b479aa4cf67c9d4bb146570d6fe47152727c888cd86cb04585ec11e75 REPORT.md
ac2c112fea3d1fbfeaf6c373007a281809c15f24b8df2a4c2d4690226148c41d OUTPUT_VALIDATION.json
258185105c2b93eae5aada37a74b7321b08c74f9c522dd4f2734471125a151bb core_full_H.csv
a529d62f4b3071298d0a0eee2845ae0639788e82992a3e4a3fb76275a20da3e6 core_crossings.csv
eb1deb0f9da2553abf77a6d778ee8bb7e59cb25dfa93c128e7c8ade0ea3d628c core_crossing_values.csv
678af3f11f49eaacbd465fb3c7222a24b4be3ebc999cad8999b8a64059dc609b core_j3.csv
beed378d242b92b4b81f31cd46c0fde442033494edf668bb41b7e9cb88014d78 core_j4.csv
afbf8c0accf417dce1a93f1ca876b2f69d22f00d22274da59dd891dc19a2adcd core_j4_analysis.json
230d36be6843b29c8e82cffcc8ae2402247b9bdb72aa7fd8efbe015b40a9d451 certificate_witness_N10.json
aa99b78fca072fc53aee5be6c021322acb7d00068318e82a88179c825fb7a714 certificate_witness_N20.json
f120a529570922ed619f26f73b89deed7fea26193facf66a5e0068b99a6d53a5 certificate_witness_N50.json
33d4c8079414ad4b7ca096629f5acc2cb32fcf059e98591986e140783980ce84 certificate_witness_N100.json
04a66803bb467b1a55da8ce5f94f49e10c657313e2c204f9143402015e9419a9 certificate_witness_N200.json
7ccc45be99d484f6c5fc7ee3b9b9d81a6e522a44eed0b8c1a7f4d07b5f6dc9ad certificate_witness_N500.json
03b44ac41bdcb50e0ceb123113a56931aae87fe94872762553d4dab2741c6205 certificate_witness_N1000.json
a7a05afc701a8530f4da325582fb63d28c1a287fafc3c5dc5535232364c3c640 certificate_witness_N2000.json
```

## Post-review repeat of derived validation

Root repeated `validate_outputs.py` after the final source-bound scan. It exited
0; every field of OUTPUT_VALIDATION.json is identical to the reviewed record
except elapsed seconds. The table above retains the hash actually reviewed.
The final fresh validation hash is `2d1d9607adbeef3a8c0fa7b561cac336d1b3d79223ca8c822d22a334a54f2b9c`.
No mathematical source, certificate witness, report, or judge decision changed.
