# Слабейший запрошенный source-consumer (13)

DIAGNOSTIC_NEVER_A_PROOF. Это запись достаточного интерфейса из вердикта,
не заявление о глобально слабейшем из всех возможных RH-критериев.

Зафиксированы исходная K_m, N=m, L=log m, нулевое продолжение и физическая
L²-норма. Пусть M_m=min(m,ceil(8L²)), H_m — вещественные чётные cosine
синтезы с n<=M_m, удовлетворяющие ТОЧНЫМ

    f(L/2)=0,       integral_(-L/2)^(L/2) cosh(x/2)f(x)dx=0.

Положим

    P_m[f]=sum_(p^k<=m) (log p)/sqrt(p^k) Q_f(log(p^k)),
    Q_f(s)=2 integral_R f(x)f(x+s)dx.

Включены все k>=1; endpoint n=m имеет Q_f(L)=0. Нужна только следующая
ВЕРХНЯЯ сторона, равномерная по всем f в указанном H_m:

    для каждого epsilon>0 существуют C_epsilon<infinity,
    m_epsilon и неограниченное множество S_epsilon⊂N такие, что
    P_m[f] <= C_epsilon m^epsilon ||f||²
    для всех m∈S_epsilon, m>=m_epsilon, и всех f∈H_m.       (13)

S_epsilon, C_epsilon не выбираются отдельно для каждого f. Семья m может
зависеть от epsilon. Пространство H_m и source P_m не зависят от
гипотетического нуля, момента или желаемого знака. Эта версия слабее
требования eventual bound на всех m; её хватает, поскольку adverse
свидетель (3) существует на ВСЕХ sufficiently late m.

Из (12), K|H=B-P|H и B>=-c_*I получаем
`K|H>=-(c_*+C_epsilon m^epsilon)I` на S_epsilon.
Если есть фиксированный off-line нуль с eta>0, (3) даёт
`lambda_min(K|H)<=-a_rho m^(eta/2)` на всех поздних m.
Выбор epsilon=eta/4 противоречит этим двум оценкам на неограниченном
S_epsilon. Это receiver-импликация при наследуемой source identity.

Можно поставить любой фиксированный polylog upper либо
exp(sqrt(log m)) upper вместо (13): они subpolynomial. Не нужны
двухсторонняя ||P_m||, constant floor на всём J_m-perp, all-P extension,
capacity lower или bounded centered residual с постоянной ценой.
Одна фиксированная положительная степень m^alpha не исключает
произвольно малое eta данным сравнением.

С arch-bound (12) интерфейс эквивалентен соответствующему
subpolynomial lower на K|H; с bounded higher-power return и (16) —
subpolynomial lower на полном R=q-Gtilde. Ни один из этих favorable
source bounds в данном аудите не доказан. При принятом классическом
Weil/source контракте RH дала бы K>=0 и P<=B, но это обратная условная
проверка интерфейса, не основание использовать его сейчас.
