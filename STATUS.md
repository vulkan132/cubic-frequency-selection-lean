# P0 形式化：检查点 F35

目标状态：进行中。**尚未完成 P0 的形式化证明。**

已从论文原文与原 Phase 12 契约建立精确目标。P0 的正下界先于 N、f、theta
确定；强加权捕获的统一有限列表先于原始数据确定。圆周频率、全部标签、原函数、
原权重均保留。两个目标本身尚未证明，也没有被当作公理使用。
已证明完整的条件性归约 WeightedCapture -> P0；该归约明确要求加权捕获作为前提。

## 已完成的证明范围

1109 条定理已经通过 Lean 4.33.0 检查，其中包括明确带前提的条件性归约：

F35 新增 43 条定理，证明实际交换子子群 [H,H]=[G,G]×W；其中实数倍
由实际交换子产生，没有把群子群直接视为实子空间。给定 G 的幂零性和 F34
的实际三角坐标条件，已证明 class(H)<=class(G)+R*(D+1)^m+1。
每个实际连续实值特征的纤维限制已证明实线性并湮灭 W；原观测曲线的源项
因此精确消失。格点上的整数性与非平凡性也传到实际分量。拓扑取真实乘积
拓扑，V 取函数空间的逐点子空间拓扑；完整 Lie/Malcev 拓扑接口仍须接通。
实际仿射例子证明交换基群仍可产生非零纤维交换子。完整有理呈现、W 的
有理性、完整格点与有界基、观测边界分析、一般结构下降和原频率结构实现
仍未完成；P0 与 WeightedCapture 仍 OPEN。详见 OBSERVATION_NILPOTENT_INTERFACE.md。

本轮按用户 2026-09-12 的要求优先形式化论文核心。外部深定理保留为明确输入，
不在本阶段展开证明，不作为新增公理，也不计作已证明。F21 新增 24 条定理，
将原响应到正原权重实七阶立方的核心推导接通，唯一新增的外部前提是
CyclicConcatenationInput。F22 再新增 28 条定理，补齐低权重及碰撞删除、
精确 q^8 计数、水平纤维筛选，以及给定匹配子集后的原质量和响应恢复。
F23 新增 39 条定理，证明有限 Schur 估计、原完整水平块的 1/N 界、任意逐点
掩码压缩，以及由实际大块数量条件推出原小弧算子估计。它保留平方根损失，
并将误差参数和规模阈值置于 N 及原始数据之前。结构模型的大块数量条件仍未证明。
F24 再新增 31 条定理，补齐原算子的收缩性与支撑上的圆周误差稳定性、任意逐点
子模型指派、主弧传递，以及给定实际大块计数和子模型后的冻结单步合并。
该合并不证明结构子模型的产生、各个下降步骤或统一终止。
F25 新增 42 条定理，完成覆盖原箱体全部边界的有限竖直扩张、原块精确恢复、
完整相位的大块估计，以及从实际压缩大块提取许多非零位移和各自原基点根。
这些常数先于 N、全局频率场、原频率场、掩码与水平基点确定；没有同步不同位移的根。
F26 新增 25 条定理，接通线性竖直模型的真实相位、正反块关系、N^(-5) 斜率关系，
以及无斜率关系部分的实际块计数和小算子估计。全程保留原响应与任意逐点掩码。
本轮复用已证明的三次 Weyl 结果，没有引入新的外部深定理。关系行上的子模型、
次数零的 Fourier 起始估计、高次模型和一般结构下降仍未闭合。
F27 新增 9 条定理，构造关系行上的实际有限子模型及原点指派，保留全部有理根分支。
子模型只在竖直变量上为常数，仍保留原截距对水平位置的依赖。将它们接入已证估计后，
完整线性冻结归约至明确的次数零核心命题 UniformConstantFreezing；该命题尚未证明。
这些检查点不是 P0 或完整论文的形式化证明。

F28 新增 23 条定理，证明次数零模型的精确 Fourier 通道：平移乘子、逐频率能量
汇总、循环输入的单射与零扩张、全部原端点和完整原响应的恢复。群大小归一化精确
消去，保留二次 Fourier 相位；先估计完整循环输出，再限制到原竖直箱体。
UniformHorizontalConstantFreezing 在相同 Q、N0 下推出次数零估计，横向估计本身
仍未证明。精确横向 Gram 核、同时控制三次与二次系数及真实大项计数是下一步。

F29 新增 31 条定理，完成上述横向核心，并从明确的外部两系数 Weyl 输入推出次数零
和完整线性冻结。最终定理不再另行假设次数零估计；外部输入及其文献/库表述转换
本身未证明，不作为新增公理。高次与一般结构模型仍未完成，P0 与 WeightedCapture 仍 OPEN。

F30 新增 26 条定理，定义真正的普通多项式原模型并恢复同一原响应，证明所有 D>=2
的实际完整相位与顶次系数 -3*k*(2*h)^D*a_D(x+h)。在明确的外部最高次 Weyl 输入下，
实际大块给出当前行顶次系数的 N^(-(D+3)) 关系，保留原根、正整数倍及参数顺序。
高次的 h^D 单项式返回、实际低次子模型和次数归纳仍未完成。

F31 新增 19 条定理，构造真正的低次多项式子模型，保留原低次系数、全部圆周根
分支和实际逐点指派。列表数量先于 N 和系数；在原关系行上误差为 epsilon/(2*N^3)。
原大块计数、无关系算子及完整次数归纳已接成条件性定理，除两个明确外部 Weyl
输入外，仍显式要求未证明的内部核心命题 MonomialDenseReturns。该命题不是外部
深定理豁免，也不是公理。现在普通多项式冻结的主要内部缺口收束到高次返回；
一般结构模型、结构下降和 P0 仍未完成。见 ORDINARY_DESCENT_INTERFACE.md。

F32 新增 13 条定理，完整证明 MonomialDenseReturns，包括 m=D 的临界情形。
证明先从实际原返回中提取短簇，通过与中心无关的整数插值获得有界正整数倍，
再用实际同号舍入分组的整数间距得到 N^(-(m+D)) 误差。没有未证明的核心或外部前提。
将该引理接入 F31 后，任意固定次数的普通多项式冻结只剩两个明确外部 Weyl 输入；
内部返回、实际子模型及次数归纳均已完成。一般结构模型和 P0 仍未完成。
普通多项式部分的准确边界见 MONOMIAL_RETURNS_INTERFACE.md。

F33 新增 35 条定理，开始接入一般结构观测。已构造实际平移不变函数空间及其
差分空间 W，证明论文所用右半直积的群公理、整数值子群及格点修正的精确顺序。
固定观测已定义在真实陪集商空间上，其圆周值对每个右格点变换保持不变。
实际观测曲线与原完整大块相位、原 lag 标签求和严格相等；没有同步不同 lag 的根。
已证明给定共同降次旗标时 1 属于 W，以及该条件下源三次项在所构造的水平特征中消失。
省略曲线平移项会造成精确 1/2 圆周误差的仿射反例也已机器检查。
一般有理模型的旗标、W 的真子空间与有理性、完整格点结构、H 的幂零性、观测的
边界分析、特征分类与有界性仍待证明；本轮的函数空间不被冒充为这些完整结构。
一般结构下降和 P0 仍未完成。见 OBSERVATION_GROUP_INTERFACE.md。

F34 新增 33 条定理，从实际多项式支持出发证明低权重坐标修正导致任意多项式的
平移差分严格降次，包括零多项式与最高项抵消。通过实际坐标求值构造观测空间的
共同旗标；对于 m 个三角坐标、修正项次数界 D、观测次数界 R，显式权重为
(D+1)^i，旗标高度为 R*(D+1)^m+1，均与任意实系数和具体平移无关。
在这些明确的三角坐标条件下，已消除 F33 的抽象旗标前提，并证明 1 属于 W 且
W 为真子空间。W 与整数值子群的交在后者中饱和也已证明；这里的消去仅在实向量
空间中进行。三角替换的差分不降低普通次数的精确反例说明必须使用权重。
尚须把一般有理 Malcev 坐标的完整呈现接入这些坐标条件，证明 W 的有理性、完整
格点和基、观测群的幂零与有理结构，以及一般结构下降。P0 仍未完成。
见 COORDINATE_FLAG_INTERFACE.md。

- 五条相位代数恒等式，包括四阶差分消去三次多项式和线性碰撞的因子 8。
- 原箱体的基数、相位模长、圆周相位与原复指数公式的一致性。
- 全标签距离的非负性与平方恒等式，原响应的一致有界性。
- Cauchy–Schwarz 比较及同一原函数的完整响应转移。
- 任意逐点指派下的加权有限选择、由已给定捕获推出固定频率响应。
- 原权重到原箱体平均的比较，以及每个有限尺度的 delta/N^3 下界。
- 从原响应构造正质量权重、逐点相位对齐、大小尺度合并及完整量词的
  WeightedCapture -> P0 归约。
- 全标签距离的对称性、三角不等式及
  d_(3,N)(a,b) <= 2*pi*N^3*||a-b||_T。
- 圆周最近实代表、精确根分解、带误差的全部 q 个根分支及其全标签距离界。
- 自然 N^(-3) 网格的舍入误差和整数指派的实数大小界。
- 一个精确分支反例：2*(1/2)=0 mod 1，但 ||1/2||_T=1/2。
  这是错误除法规则的反例，不是 P0 的反例。
- 主弧上的统一有限候选列表：索引集合只依赖 Q 与精度参数，N 仅进入候选值；
  列表在原频率、原函数及模型数据之前选定。
- 任意逐点模型指派的加权能量界、剔除小弧点后的原权重质量下界，以及
  s = eta*sqrt(c)/(8*sqrt(J)) 对应的精确能量预算。
- 每个原抛物线端点在 [2N]×[2N²] 中的精确索引、原函数的输入能量界
  4*N^3，以及有限算子作用与原完整响应的逐点相等性。
- 从明确给定的模型近似及有限算子估计，到正原权重的原频率有限捕获，
  已连成完整的条件性末端定理。
- 原端点的单射性与碰撞坐标、有限复数算子的伴随恒等式、AA* 的原标签碰撞展开，
  以及同一水平纤维的精确 I/N 对角块。
- 内积对第一个变量线性的约定下，b = sigma*conj(lambda) 与原加权响应
  的精确配对，及 ||A*b||² >= |R|²*N³/4 的第一步伴随下界。
- h=0 贡献精确等于 ||b||²/N，受 sum(sigma)/N 控制；剩余有符号贡献
  先按完整水平纤维分组，再取绝对值。
- sigma = N³*mu*1_D 的原权重支撑、界和质量恒等式；原响应的正性只在
  非零权重处使用。任意保留集合 D 的原质量 m = mu(D) 均被精确保留。
- 论文第一条 TT* 下界 sum_(x!=x') |J_(x,x')| >=
  N³*max(|R_D|²/4-m/N,0)，以及单个水平块的伴随 Cauchy–Schwarz 界。
- 第二次伴随显式限制在 x,x' ∈ X；从 D 的水平支撑包含于 X 的条件证明
  窗口外第一次配对为零，再对至多 N² 个完整水平块使用 Cauchy–Schwarz。
- 非平行抛物线的固定基点碰撞标签唯一，每个非零核元素的模为 N^(-2)，
  每行至多 N 个非零元素，其平方能量至多 N^(-3)。
- 第二次有限 Gram 展开的精确对角拆分；第二次对角项非负，归一化后
  至多为 mu(D)/N，与第一次 h=0 的误差分别证明。
- 原矩阵指标下的有符号统计量 S_fin 保留 sigma_z*sigma_w 和
  lambda_z*conj(lambda_w)，并满足 max(|R_D|²/4-m/N,0)² <= S_fin+m/N。
  现已通过完整的标签双射与有限求和重排，证明它等于下述 lag 指标统计量。
- 在 |h| <= H <= N 和给定安全区条件下，抛物线目标与 2hk 位移均落在原箱体。
  已证明存在对应的实际有限基点，以及 h!=0 时竖直零位移当且仅当 k=0。
- 一个精确有限算子反例：输入及配对均为零，伴随向量的平方能量仍可为 1。
  这解释了第二次伴随必须显式保留 X；它不是 P0 的反例。
- 上下边带的精确有限计数和原质量损失 <=6H/N；边带可能重叠时该界仍有效。
  M=ceil(64/kappa)、H=floor(N/M) 给出损失 <=kappa/8。
- 至多 M 个水平块构成完整分割，每块直径 <=H，末块保留其全部合法端点。
  已证明存在安全窗口 D=X×Y，原质量至少 c=kappa/(4M)>0。
  M、c 在 N 及原始数据之前确定，并保留 X 的实际整数区间性质。
- 从所有原始 Admissible 数据统一选出上述安全窗口，使 S_fin >=2*zeta>0。
  可取 zeta=eta^4*c^4/256，N0=ceil(128/(eta^4*c^4))+1；这些常数先于
  N、f、theta、lambda、mu 确定。原非零权重点的响应正性随结论保留。
- 原单块公式的整数标签恰好为 I_h；每个原碰撞出现一次，且每个有效标签
  对应一个实际原目标。两个标签的第二源点为 y+2h(r1-r2)，也在原箱体内。
- 完整 Gram 行的双标签展开及其有符号非对角项。h!=0 时，竖直对角项
  恰好对应 r1=r2；核乘积相位和 N^(-4) 系数均逐项验证。
- (r1,r2) <-> (k=r1-r2,r=r2) 在完整合法标签域上的双射与求和等式。
  k=0 恰好对应相等标签；|k|>=N 时 lag 标签集合为空。
- 原字段的整数坐标表达与每次有效原基点读取严格相等。频率只在圆周上运算，
  未选择实提升，也未丢弃任何圆周根分支。
- 整个安全窗口上 S_fin = S_lag，总归一化为 N^(-6)。S_lag 显式保留
  x,x'∈X、x'!=x、全部原 y、k∈[-N,N]、r∈I_h∩(I_h-k)、k!=0，
  以及两个原权重和两个相位对齐因子。零权重行不要求额外安全条件。
- 统一正下界已经通过该等式转移：同一组先于全部原始数据选定的常数保证
  S_lag>=2*zeta>0，同时保留安全窗口原质量及原非零权重点的完整响应。
- t=r+k-h 已提升为完整有限求和双射。新的外层条件恰好为 t,t+h∈[N]，
  内层为 [t-N,t-1]∩[t+h-N,t+h-1]，包括 k=0；没有新增或丢失标签。
- 每个 k=0 原项精确等于 sigma_z²*|lambda_z|²，故非负。重新插入的完整
  lag 对角贡献 D_lag 已直接由原权重证明 0<=D_lag<=mu(D)/N。
- 重排后的原相位精确分解为外层相位乘以 g(k)e(P(k))，共享目标为
  y+h²+2ht；B 的分母严格为 N，未改为实际内层区间长度。
- 已证明 S_lag+D_lag=N^(-5)*外层原加权实部求和，并证明 |g(k)|<=1、
  |B|<=1。取模时只使用非负原权重，随后仍保留这些权重。
- 已将外层 t 区间改写为全部原 Fin N 标签上的条件求和，得到 x,x',y,t
  原有限指标上的模长平均。该平均至少为 2*zeta；常数、阈值先于全部原始
  数据选定，原质量、安全窗口及原非零权重点的完整响应仍保留。
- 原竖直区间在 Z/qZ 中的嵌入是单射，像恰好对应整数代表 1,...,N²。
  像外原权重为零；安全支持上的 2hk 位移及共享目标没有绕回，循环群中的
  g、P、B 与相应原表达严格相等，整个竖直加权求和也严格相等。
- x' 到 h 的完整水平重排已证明。[-N,N] 中的非零位移恰好有 2N 个；
  不到达 X 的位移保留为零项，全部 x,h,y,t 的采样空间基数为 2qN³。
- 原有限模长平均 = (2q/N²)*循环群模长平均。形式化采用先在原有限域取模，
  再进行这个精确转换的顺序；整个过程中保留原权重和实际原字段。
- 统一常数先于 N、q 和全部原始数据确定。对每个 N²<q<=128N² 的非零模数，
  循环群模长平均至少为 zeta/128>0；安全窗口原质量及原完整响应同时保留。
- 采样权重始终位于 [0,1]。循环群上所有参数处的 |g|、|B|<=1 已证明，
  包括后续平滑可能访问的位移。由 Mathlib 已证明的 Bertrand 定理，
  对每个 N>0，已证明存在严格满足 64N²<q<128N² 的素数模数。
- 对任意整体有界复序列，任意整数平移 d 的区间求和误差至多 2|d|；
  正负平移及空区间均包含在证明中。实际 K_(h,t) 是一个整数区间，归一化
  分母仍为原 N，不要求其长度等于 N。
- 四个独立平移的完整采样空间大小为 (2*ell+1)^4。平滑与 k 求和精确交换，
  总误差至多 8*ell/N；ell=floor(a*N/64) 时至多 a/8，也包括 ell=0。
- 对实际循环 lag 序列进行平滑后，原权重的模长平均至少为 7a/8。
  M,c,a,N0 在 N、q 和全部原数据之前选定；同一安全窗口的原质量及
  原非零权重点的完整响应仍出现在统一定理结论中。
- 原三次圆周相位已显式分解为四个模长一因子，每个因子独立于相应坐标。
  已证明整个实际平滑序列等于相应乘积表达，共享目标频率保持固定；
  这一步仅进行整数倍圆周运算，没有选择实提升或删去根分支。
- 盒式 Cauchy–Schwarz 已对任意维数通过归纳证明。每次复制坐标后的精确
  配对求和、剩余面因子的模长一性质及独立性均保留，所有有限平均分母明确。
  递归盒矩非负；对应盒范数的 2^d 次方严格等于 d 维盒矩。
- 四维情形已应用于原循环 g 的四平移函数，原平滑项的模长受其盒范数之和
  控制。原权重只在形成非负盒范数之后删去。扩大到全部 k∈[-N,N] 的
  归一化比率为 (2N+1)/N<=3，整个外层采样空间大小为 2qN³(2N+1)。
- 已通过有限平均的矩不等式证明全局盒矩平均至少为 (a/4)^16>0。
  M,c,a,N0 仍在 N、q、f、theta、lambda、mu 之前确定；同一安全窗口的
  原质量、原完整加权响应和原逐点响应都保留在统一定理结论中。
- 递归盒矩与完整 Boolean 顶点乘积的复数值等式已对任意维数证明；
  共轭符号与 (-1)^(顶点重量) 一致，重复顶点及其重数完整保留。
  四维情形恰有十六个因子，四对平移参数的采样空间大小为 (2*ell+1)^8。
- 整个循环立方平均已通过显式双射 Y=y+2hk 重定根，逆映射为 Y-2hk。
  不使用 2h 的乘法逆元，也不要求这一步的模数为素数。
- 十六个原权重的乘积、交替相位对齐因子及 t 相位已严格分离。
  相位是圆周值的三次多项式；三次系数正是负的带符号原频率立方和，
  不依赖 k。权重乘积及对齐因子也不依赖 t 或 k；所有圆周运算保持原值。
- 通过完整指标双射将全部原 t 标签的平均置于内层。所得三次指数和模长的
  原立方加权平均至少为 (a/4)^16；十六个权重仍在平均中，常数先于 N、q
  和全部原始数据确定，原安全窗口质量及原完整响应随结论保留。
- 只要立方权重乘积非零，每个顶点均对应 D 内的实际原基点，原 mu 非零，
  循环字段读取严格等于该点原 theta、lambda 及 N³*mu，原完整响应成立。
- 线性逆 Weyl 估计已经证明：任意圆周斜率 a、常数项 b，完整平均模长
  >=rho>0 时，||a||<=1/(2*rho*N)。同一结论适用于任意实际整数区间，
  分母仍为原 N。证明来自精确几何级数及 4*||a||<=|e(a)-1|。
- 完整标签配对到位移的恒等式给出 N*|平均|²=sum_h Re(相关(h))。
  h=0 贡献单独控制为至多 1；当 N*rho²>=2 时，[-N,N] 中至少
  N*rho²/4 个非零位移的相关模长 >=rho²/8。两个符号均保留。
- 已机器证明 N=1 的精确反例：完整平均模长为 1，所有非零位移相关却
  均为零。这说明上述数量结论不能无条件用于小尺度；它不是 P0 的反例。
- 二次及三次圆周多项式的降次恒等式已证明，实际交叠区间恰好为
  [max(1,1-h),min(N,N-h)]。常数项、低次项和原 N 分母全部保留。
  大二次平均给出至少 N*rho²/4 个原位移，满足 ||2h*a2||<=4/(rho²*N)。
- 稠密仿射回归的第一步已证明：在明确的有限计数条件下找到两条相距
  <Q 的实际回归，消去相同常数项，得到 0<q<Q 及 ||q*a||<=2*epsilon。
- 稠密仿射回归的定量放大现已证明：epsilon*N<=C、至少 rho*N 条实际
  回归时，得到 ||q*a||<=E*epsilon/N。Q、E、N0 都先于 N、a、b、epsilon
  和回归集合确定。证明按实际舍入整数分组，再用同组整数标签的端点间距。
- 二次及三次最高系数的逆 Weyl 定理已经证明，分别给出 N^(-2)、N^(-3)
  误差和统一有限的正分母范围。每个 N>0 都包含在内，小尺度用圆周半周期
  界吸收；二次估计在实际交叠区间上仍使用原 N 分母。
- 三次降次后只在实际成功分母的同一个分组上继续回归，并保留该组的
  明确密度。取统一分母上界的阶乘，得到先于 N 和全部系数的共同正分母 d。
- 该估计已应用于原立方时间平均。被控制的是交替原频率立方和的三次
  系数，结论为 ||d*cubeCoeff||<=E/N³，不是单点原 theta 的捕获。
- 满足这一条件的立方仍有至少 (a/4)^16/2 的原加权平均。十六个权重
  全部保留，M、c、a、d、E、N0 先于 N、q、原 f、theta、lambda、mu；
  同一安全窗口的原质量、原完整加权响应及逐点原响应仍在统一结论中。

- 已通过完整有限双射消去 k 平均，无额外归一化损失。将 h 和四对平移
  参数同时取负时，每个实际顶点逐点不变；故正 h 标签平均与原有符号平均
  严格相等，全部十六个权重和原锚定系数均保留。
- 对八个独立平移坐标，已证明重新采样单个坐标保持均匀平均。两个不同
  Boolean 顶点总有一个分离坐标；固定其他参数后，碰撞至多允许一个取值。
  这里明确使用 2*ell<q、素数 q 和 2h 在 Z/qZ 中非零。
- 单对碰撞概率至多 1/(2*ell+1)，全部 120 对无序顶点的联合碰撞概率
  至多 120/(2*ell+1)。这些是对任意合法参数的证明，不是有限采样测试。
- 已证明一个准确的必要条件反例：q=7、ell=1、h=7 时，整数 h 非零、
  平移区间仍单射，但 2h 在模 7 下为零，单对碰撞概率为 1，超过 1/3。
  这否定了删去非零模步长条件的规则，不是 P0 的反例。
- 已给出先于 q 及全部原始数据的统一阈值，保证正标签步长非零、平移区间
  单射以及碰撞预算。删除碰撞只损失其概率，全部原权重继续保留。
- 对原范围内的素数 q，十六个顶点互异且满足 ||d*cubeCoeff||<=E/N³ 的
  立方具有至少 (a/4)^16/4 的原加权平均。M、c、a、d、E、N0 先于 N、q、
  f、theta、lambda、mu；原安全窗口质量、原完整加权响应和逐点响应保留。

- 现已固定每个圆周值的 [0,1) 代表及其最近格点整数，证明全部 57 种
  允许修正都满足同一格点和误差界。八个正号与八个负号的数量已精确核查。
- 对同一组十六个舍入值，已证明 S=l*M_lift+r，|l|<=8、|r|<=9；
  一个允许的局部修正使实数交替和严格为零。整数分支没有删去。
- 全局点指派限制到任意互异顶点族时仍均匀，已由完整双射证明。
  每个成功立方的局部修正概率至少 57^(-16)。有限平均交换与原非负权重
  给出一次全局选择；所有立方共享每个点的同一次选择，不要求立方相互独立。
- 全局实值提升 F 已完成：M_lift=floor(N³/E)>=9，所有点 F∈M_lift^(-1)Z，
  |F|<=3，原扩展权重为零处 F=0；正权重处 ||F-d*theta||<=19E/N³。
  实数四阶差分为零的立方仍有至少 (a/4)^16/(4*57^16) 的原加权平均。
- 该提升定理中的 M、c、a、d、E、N0 全部先于 N、q 和原始数据选定；
  同一安全窗口的原质量、原完整加权响应和逐点响应仍在结论中。F 提升 d*theta，
  这一结果尚未给出原 theta 的统一有限捕获。
- 一个准确的量词反例已核查：每个事件分别有成功选择，并不推出存在
  一次选择使所有事件都成功。本证明取得的是一次选择下的正加权平均。

- 完整非整数频率网格 j/1024 的精确正交性已证明。对任意 d<=7，
  同一格点函数的实数差分为 k/M_lift，且 |k|<=384M_lift<1024M_lift；
  频率平均恰好检测实数差分为零，包括重复顶点。
- 两个准确反例已核查：全部整数频率无法排除非零整数差分；缺少大小界时，
  当前完整网格也无法排除非零差分 1024。这些是错误中间规则的反例。
- 任意有限多重集位移的局部矩非负、对应范数的精确 2^s 次方，以及
  有界函数的范数 <=1 已证明。实际 Q_h=2h[-ell,ell] 的所有重数均保留。
- 原十六权重乘积的频率平均已精确等于原实零立方质量；同一 F 的
  局部四阶范数十六次方平均至少 beta=(a/4)^16/(4*57^16)。
- 至少 beta/2 比例的实际 (x,j) 对满足 h 上的局部四阶范数平均 >=beta/2。
  统一结论继续保留同一 F、原安全窗口质量、原完整加权响应和逐点响应，
  所有常数及阈值先于 N、q 和全部原始数据确定。

- 有限阿贝尔群上的完整字符正交、傅里叶反演和 Parseval 恒等式已证明。
  变换使用群上的均值，反演使用字符之和；没有混淆两个归一化。
- 参数映射 r:A→G 的密度为 |G|*重数/|A|，保留每个重复表示。
  原独立参数差分与差分密度的加权均值完全相等，并已扩展到任意维。
- 局部矩已精确改写为带实际差分密度的全局立方体均值，再展开为非负
  傅里叶系数的加权和。系数总质量等于密度平方均值；表示重数界 K
  给出平方均值 <=|G|*K/|A|。
- 条件性比较 localCubeMoment_bound_of_twisted 已证明；它仍显式要求
  每个字符扭曲立方体的模长 <=L。F19 已为阶数至少二证明该估计，
  并在新的完整比较定理中消去此额外前提。
- 有界面函数的 box Cauchy–Schwarz、平移下的平方和比较，以及一个
  用原概率质量替代均匀测度密度会破坏比较式的精确反例均已证明。

- 所有阶数 s>=2 的字符扭曲全局立方体估计已证明。二维基例使用
  交叉相关的傅里叶变换、调制的频谱平移、Parseval 和平方和比较；
  高阶使用完整首坐标差分递推。没有假设未证明的混合 Gowers 不等式。
- 完整多重集比较已证明：实际参数密度满足 E(nu^2)<=C 时，局部 s 阶矩
  <=C^s*全局 s 阶矩，s>=2。还给出精确根范数界及从局部正范数到
  全局正矩的定量下界。该比较本身不要求 H 有界。
- 两元素群上的精确反例证明一阶不能套用同一字符扭曲估计：扭曲平均
  可为 1，而未扭曲的一阶矩为 0。它不是 P0 的反例。
- 同一实函数 F 的完整频率平均已在任意 1<=s<=7 阶全局立方体上核查。
  实际循环群七阶矩平均恰好等于全部原权重保留的实零七阶差分质量。
  此恒等式本身不产生统一正下界；F21 将其接到以下条件性正下界。
- 实际整数及循环群配对位移的表示重数至多为 1+2*A²；没有把参数多重集
  合并成像集。原尺度下的取模不产生额外碰撞。
- 小标签及大公因数配对的总比例至多 3/A。取 A=ceil(12/u) 后至多 u/4；
  尾和用有限望远镜求和证明，包括空区间情形。
- 实际配对密度满足 E(nu²)<=C=2^24*(1+2*A²)/(u²*a²)。配对局部均值
  大于 u 时，得到全局七阶矩至少 (u/2)^128/C^7。
- 在显式外部拼接输入下，统一定理给出正原权重的实零七阶立方质量。
  一个 F 用于全部频率和标签，常数先于 N、q、f、theta、lambda、mu，
  原安全窗口质量、完整加权响应和非零原权重点的完整响应均保留。
- 七阶立方的任意不同顶点对碰撞概率至多 1/q，全部 8128 个无序顶点对
  给出总损失 <=8128/q。这在任意有限交换群中成立，不需要除以群元素。
- 删除任一顶点权重小于 tau 的乘积损失至多 tau，强于原文使用的 128*tau。
  tau=chi/512 和统一碰撞阈值留下平均至少 chi/2 的互异、高权重、实零立方。
- 精确无权计数的分母为 q^8；统一原数据定理选出至少 chi*N/4 个水平纤维，
  每个至少有 (chi/4)*q^8 个这样的立方，同一 F 和完整原响应继续保留。
- 给定每个选中纤维上的高权重子集 S_x，正阈值保证所有点都对应真实原基点。
  若 |H|>=rho*N、|S_x|>=cModel*q，原质量至少 64*rho*cModel*tau。
  给定 F=G 的匹配关系后，圆周误差转移到 d*theta-G，完整原响应保持。
  这些是运输结论；没有把任意 G 宣称为 nilpolynomial，也没有断言结构模型存在。

F23 进一步完成有限算子接口：

- 行列 Schur 界、双向伴随能量转换，以及按完整水平块分组的 Schur 界。
- 原每个非对角块的行和与列和均至多 1/N，故块范数至多 1/N；对角块为 I/N。
- 任意逐点复数收缩掩码在块两侧的精确公式与范数控制。
- 掩码支撑在保留水平行上时，每个保留行至多 rho*N 个实际压缩大块，其余保留的
  非对角块范数至多 v/N，推出平方能量界 rho+v+1/N 和对应掩码算子范数界
  sqrt(rho+v+1/N)。
- 该数量条件对实际小弧掩码成立时，推出原 FiniteMinorEstimate；完整原 f 与
  所有原标签均保留。rho、v、N0 可先于 N、Q、p 选定。
- K=1/2、R=1/4 的精确反例证明，原算子范数界不能漏掉平方根。这不是 P0 反例。

F24 完成原算子稳定性与条件性冻结合并：

- 对任意原频率场，完整有限响应算子是收缩算子。掩码非零处所有原标签的相位
  误差至多 epsilon 时，差分平方能量至多 epsilon^2 倍同一个原输入的能量。
- 支撑上的圆周误差 epsilon/(2*pi*N^3) 保证上述逐标签条件；输入函数与标签不变。
- 任意逐点子模型指派具有精确的分片能量恒等式，允许不同子模型具有不同 Q_i。
  子误差 s/(3*sqrt(J)) 精确对应合并后的平方预算 (s/3)^2。
- Q>=2*Q_i 且频率足够接近时，原父模型在小弧上保证选中的子模型也在小弧上。
  论文的 0<s<=1 条件与 a0=s/(12*pi) 的误差尺度均被保留。
- 无关系部分、替换误差、子模型部分分别按 s/3、s/12、s/3 合并，得到原
  FiniteMinorEstimate。统一数字参数先于 N、J、Q、原频率、子模型和指派确定。
- 此结论仍要求实际压缩大块数量界、子模型近似及各子模型的小弧估计；没有将
  这些前提当成结论。两个精确反例核查了不能省略 J 能量损失或主弧传递的接近条件。

F25 完成实际相位的大块接口：

- 将竖直输入扩大到 [1-N^2,2*N^2]，覆盖每个原基点的全部合法原标签目标。
  原输入的零扩张保持能量，扩大后的块精确恢复原水平块，适用于任意逐点压缩。
- 完整双标签到位移的相位恒等式保留四个圆周因子及 N^(-4)；零位移单独计入 N。
  一个精确二项反例说明，不能直接用完整和的模控制截断和的模。
- 每个位移相位和的上界 M(k) 给出平方能量系数 (N+sum_{k!=0}M(k))/N^4。
- 原压缩块超过 v/N 且 N*v^2>=2 时，至少 N*v^2/4 个非零位移满足 |k|<N，
  并各有一个原基点根使完整相位和至少为 N*v^2/8。统一版本的 c=v^2/8 与 N0
  先于 N 及全部数据确定。不同位移无需同根；其他相位取值点可在原箱体外，必须
  使用真实的全整数模型公式，不能将其当成新增原响应或保留连接。
- 本轮没有证明结构模型的大块数量界、实际降次或统一终止。
  精确作用域见 WIDE_BLOCK_INTERFACE.md。

F26 完成线性模型的无关系部分：

- 全整数线性公式与原箱体及任意实线性系数的取值精确一致；真实位移相位的四个
  三次多项式系数全部给出，最高次系数与所选根和两个截距无关。
- 实际位移标签是完整整数区间；较短区间的三次 Weyl 估计保留原 N 分母，一个
  正分母在 N、区间和所有系数之前确定。该三次情形不使用外部 Weyl 假设。
- 保留实际分母子集的仿射返回估计将 N^(-m) 提升至 N^(-(m+1))，适用于每个 m>=1。
  这不是一般 h^D 单项式返回定理。
- 正反实际压缩块分别给出两条关系；保留 8*n1*n2 得到原当前行斜率的 N^(-4) 块关系。
  两个斜率均为 1/4 的精确反例说明，方向组合均为零时仍不能取消整数因子。
- 至少 rho*N 个实际大块推出 ||q*a(x)||<=E/N^5，q 为有界正整数；逆否命题给出
  无关系行的真实大块数量界，不再将这部分数量界作为未证明输入。
- 对每个 s>0，Q,E,N0 先于 N、所有斜率、截距和掩码确定。任意收缩掩码在关系行
  上为零时，原响应的掩码平方能量至多 s^2 倍同一个原输入的能量。
  这里 Q 是斜率分母界，不是已经构造好的原频率主弧截断。
- 关系行上的常数子模型和次数零起始估计仍未证明，因此完整的线性冻结也尚未完成。
  精确作用域见 AFFINE_FREEZING_INTERFACE.md。

F27 完成实际子模型构造和线性冻结归约：

- 主弧显式网格在保留全部分母、剩余类和舍入指标后，给出 epsilon/(2*N^3) 的
  圆周误差。没有将全标签距离界反向当作圆周误差界。
- N^(-5) 斜率关系使每个原竖直增量落入自然 N^(-3) 主弧；近似的是增量，
  不是直接认定原完整频率落入同一个主弧。
- 子模型数量 J 先于 N、斜率和截距；每个 N 的网格偏移先于所有系数，实际原点
  指派甚至先于截距场。全局子模型为 b(x)+offset_i(N)，并非与 x 无关的原 theta 候选。
- 在 s/3 无关系估计后确定 J，再以 s/(3*sqrt(J)) 调用次数零核心前提；最终
  主弧截断 2*Qchild 与最大规模阈值先于 N 和全部原系数。原输入及完整响应保持不变。
- 唯一剩余的线性冻结核心前提是 UniformConstantFreezing，它被明确写成函数参数，
  没有声明为公理，也没有作为已完成的外部深定理。作用域见 AFFINE_CHILD_INTERFACE.md。

F28 完成次数零 Fourier 分解到原响应的核心通道：

- 以概率归一化的 Fourier 系数分解平移和，保留正号乘子及二次相位；汇总后
  群大小因子精确消去，不增加模数损失。
- 原输入竖直索引在循环群中单射，零扩张保持输入能量；全部原端点与原完整响应
  严格恢复，包括边界。最终选 q=2*N^2+1，不改变原始系数或响应。
- 横向小弧掩码只依赖 x，先使用完整循环估计，再收缩到原输出；未将任意竖直
  掩码当作 Fourier 对角项。常数与量词次序不变。
- 次数零估计归约至 UniformHorizontalConstantFreezing；它仍是未证明的核心命题。
  横向 Gram 公式、共同分母的三次/二次系数控制和真实大项计数尚未完成。
  作用域见 CONSTANT_FOURIER_INTERFACE.md。

F29 完成给定外部两系数 Weyl 输入后的次数零与线性冻结核心证明：

- 真实横向核、完整碰撞标签双射、精确 I_h 相位和 N^(-2) 归一化均已证明；
  对角项为 1/N，每项模长至多 1/N，保留二次 Fourier 相位。
- 原相位的三次、二次系数由同一个 q 控制后，得到当前行原频率的
  ||3*q*h*phi(x)||<=4*C/N^2；精确反例排除只使用三次差系数的推断。
- 实际大项的位移像保持基数；带分母返回定理在指数 2 下给出原 phi(x) 的
  N^(-3) 主弧关系。其逆否命题接通真实大项计数、标量 Schur 和原完整响应估计。
- 次数零和完整线性冻结均已从 CubicTwoCoefficientWeylInput 推出；不再另行假设
  次数零核心估计。Q、N0 先于 N、Fourier 参数及原系数，所有根分支与原响应保留。
- 上述 Weyl 输入是外部解析结论的明确函数前提，未声明为公理，未证明其自身，
  也未形式化它与外部库原定理之间的表述转换。作用域见 CONSTANT_FREEZING_INTERFACE.md。

F30 完成一般次数的真实相位与单块顶次返回：

- 任意水平实系数多项式给出全整数模型，逐点恢复原有限 profile 与完整响应。
  其次数零、一次情形与 F29 的条件性冻结严格对应。
- 仿射代入保持次数界，索引为 D 的系数乘以斜率的 D 次方，包括实际低次和零系数。
  完整相位次数至多 D+2；D>=2 时顶次系数独立于各自原根。精确 D=1 反例保留例外。
- 给定 PolynomialLeadingWeylInput，实际大块先给出许多非零 k 和各自原基点根，
  在原 lag 区间上读出系数，再经实际分母纤维和已证仿射返回取得 N^(-(D+3)) 关系。
- 反向关系仅使用真实原压缩块的伴随等价；保留 3*2^D 因子与正整数倍，最终控制
  当前原水平行的 a_D，而非单点 theta。Q、E、N0 先于 N、全部原系数、掩码和原水平点。
- 外部一般次数 Weyl 输入自身未证明。h^D 的非线性返回仍是明确未完成的核心步骤；
  尚未得出高次无关系计数、低次子模型和完整次数归纳。见 ORDINARY_BLOCK_INTERFACE.md。

F31 完成实际低次子模型和条件性次数归纳：

- OrdinaryTopRelation 保留正整数倍与 N^(-(2*D+3)) 尺度，乘原整数 y^D 后进入三次主弧。
- 真实子多项式为 erase_D(P(x))+c_i；D>0 时次数至多 D-1，原非恒定低次系数全部保留。
  实际次数小于 D 及零多项式均包含。偏移和列表大小先于原系数，指派仅使用顶次字段。
- 对任意 D,N 的精确半频率反例说明不能从顶次有理关系直接删去该项；全部根分支保留。
- 在明确的 MonomialDenseReturns 核心前提下，实际非零水平位移和分母纤维给出顶次关系，
  其逆否命题给出原压缩块计数，再由已证 Schur 得到无关系部分的小算子界。
- 子模型数量先于递归目标 s/(3*sqrt(J))，各阈值和主弧截断先于 N 与原系数。
  同一原输入、全部响应标签及 s/3、s/12、s/3 预算保留；自然数强归纳严格降低次数。
- 最终全次数结论仍带两个外部 Weyl 输入及一个未证明内部返回前提，不能读作无条件
  冻结或 P0 证明。下一步见 MONOMIAL_RETURNS_PROOF_PLAN.md。

F32 完成高次返回及普通多项式冻结的内部证明：

- 所有 m>=D>=1 都有一般证明，包含临界 m=D；原 N 分母、圆周系数与正整数倍保留。
- 整数分桶得到 D+1 个实际原返回，严格重标为 H+v(i)。插值权重及整数通分先于中心 H，
  有限相对点位族给出先于 N、原频率和误差的统一界，未用有限测试代替一般证明。
- 同号筛选至少保留一半返回，负号反射保留原点来源和奇偶性。对 q*a 的最近实代表，
  实际舍入整数有统一有限范围，同一分组的整数间距给出完整 N^(-D) 增益。
- monomial_dense_returns 无未证明前提。uniform_ordinary_freezing_of_weyl 只要求两个
  明确外部 Weyl 输入，不再假设任何内部返回、子模型存在或次数终止命题。
- 一般结构输出、有限实现、结构关系与有理下降及统一终止仍是核心工作；普通多项式
  冻结完成不等于 P0 完成。见 MONOMIAL_RETURNS_INTERFACE.md。

998 条定理的完整构建和传递公理审计通过，仅出现标准基础：propext、Classical.choice、
Quot.sound。没有 sorryAx 或项目新增的未证明公理。

条件性归约所给的统一正下界是
min(((delta/2-delta/4)*c/L), delta/N0^3)，其中 c、L、N0 都在 N、f、theta
之前从加权捕获假设选定。归约证明不证明捕获假设。
delta/N^3 随尺度变化，也不能单独证明 P0。

末端定理 finite_capture_from_model_operators 给出的列表长度 L 先于 N；
每个 N 的列表 beta 先于 f、theta、模型族、逐点指派和权重。其结论保留
A' ⊆ A、mu(A') >= c/2 及全标签距离 <= epsilon。
模型族的存在和它们满足 FiniteMinorEstimate 都是显式前提，尚未证明其统一存在。

## 下一步与仍未闭合的接口

1. 低权重和碰撞删除、水平纤维选择、精确无权计数，以及给定子集后的原质量、
   圆周误差和响应恢复均已完成。下一步精确定义结构输出类型，接入明确的实近似
   多项式外部输入，并核对统一复杂度和素数阈值。接口见 STRUCTURAL_VALUE_INTERFACE.md。
2. 线性模型的真实相位、返回估计、实际块计数、全部竖直常数子模型和原点指派已完成。
   给定明确外部两系数 Weyl 输入后，次数零与线性冻结的内部核心现已完成。
   横向核、共同分母关系的应用、真实大项计数、Schur 和原响应恢复均已接通。
   外部输入自身及其库表述转换未证明；精确边界见 CONSTANT_FREEZING_INTERFACE.md。
   F32 已证明一般高次返回，包括 m=D 的临界情形，并完成任意固定次数的普通多项式
   冻结内部链；最终定理只含两个明确外部 Weyl 输入。精确范围见 MONOMIAL_RETURNS_INTERFACE.md。
   下一步落实一般结构模型、整数多项式模及其实现，并处理一般结构模型的压缩块计数。
3. 补有限实现、实际结构子模型的产生、各个下降步骤及其统一终止。
   给定子模型与计数后的误差控制和单步合并已经完成，不能据此推断整个下降树存在。
   精确作用域见 FREEZING_STEP_INTERFACE.md。
4. Green–Tao、Tao–Ziegler、Manners 等外部深定理按用户要求保留为精确输入；
   本阶段不展开它们的形式证明。所有依赖的量词、适用范围和来源须继续记账。

当前固定 Mathlib 源码的关键词检索没有找到可直接调用的上述深层实现。
这只是当前库的检索结果，不是这些数学命题不存在形式证明的断言。
详细剩余接口见 OPEN_INTERFACES.md。

这份检查点没有给出论文全部证明正确性的确认，也没有给出 P0 反例。
U0 不在本形式化目标中；历史十二项错误三维应用继续保持 DEFERRED。

## 核查记录

- 项目定义与目标：GMZP0/Definitions.lean
- 相位代数：GMZP0/PhaseAlgebra.lean
- 响应比较：GMZP0/Response.lean
- 有限选择：GMZP0/FiniteSelection.lean
- 完整条件性归约：GMZP0/CaptureToP0.lean
- 全标签距离：GMZP0/CubicMetric.lean、GMZP0/PhaseScale.lean
- 全部圆周根与舍入：GMZP0/CircleRoots.lean、GMZP0/RealGrid.lean
- 主弧统一列表：GMZP0/MajorArcGrid.lean
- 原权重能量与质量：GMZP0/WeightedEnergy.lean
- 原输入几何与有限算子接口：GMZP0/FiniteOperator.lean
- 条件性末端捕获：GMZP0/TerminalCapture.lean
- 端点碰撞与有限伴随：GMZP0/ParabolaGeometry.lean、GMZP0/FiniteAdjoint.lean
- 原加权伴随与 h=0 拆分：GMZP0/WeightedAdjoint.lean、GMZP0/DiagonalEnergy.lean
- 原权重窗口与水平分组：GMZP0/OriginalWeights.lean、GMZP0/HorizontalBlocks.lean
- 水平窗口与第二次伴随：GMZP0/SecondAdjoint.lean
- 非平行碰撞与行能量：GMZP0/BlockCollisions.lean、GMZP0/BlockRowEnergy.lean
- 第二次有限统计量：GMZP0/GramEnergy.lean、GMZP0/SecondStatistic.lean
- 安全窗口几何：GMZP0/SafeWindowGeometry.lean
- 原边带质量与水平分割：GMZP0/VerticalStrips.lean、GMZP0/HorizontalPartition.lean
- 统一安全窗口与正统计量：GMZP0/UniformSafeWindow.lean、GMZP0/PositiveSafeStatistic.lean
- 原圆周相位与双碰撞：GMZP0/CircleCharacter.lean、GMZP0/LagGeometry.lean、GMZP0/DoubleKernelPhase.lean
- 单块完整公式：GMZP0/BlockTargets.lean、GMZP0/SingleBlockFormula.lean、GMZP0/IntegerBlockFormula.lean
- 第二源点与完整双标签：GMZP0/LagSources.lean、GMZP0/DoubleBlockFormula.lean
- lag 求和与原字段：GMZP0/LagReindexing.lean、GMZP0/OriginalFieldExtension.lean、GMZP0/LagStatistic.lean
- 统一正 lag 统计量：GMZP0/PositiveLagStatistic.lean
- 完整重定根与原零 lag 贡献：GMZP0/Rerooting.lean、GMZP0/ZeroLag.lean、GMZP0/ZeroLagBounds.lean
- 相位分解与 N^(-5) 归一化：GMZP0/RerootedPhase.lean、GMZP0/RerootedStatistic.lean
- 模长界与统一正原有限平均：GMZP0/RerootedBounds.lean、GMZP0/RerootedAverage.lean
- 循环群原字段及位移：GMZP0/CyclicOriginalFields.lean、GMZP0/CyclicLag.lean
- 水平重排和精确平均转换：GMZP0/HorizontalShiftReindexing.lean、GMZP0/CyclicNormalization.lean
- 全参数模长界、统一正循环平均：GMZP0/CyclicBounds.lean、GMZP0/PositiveCyclicAverage.lean
- 完整采样空间与素数存在：GMZP0/CyclicSampling.lean、GMZP0/PrimeCyclicModulus.lean
- 区间平移及有限平均稳定性：GMZP0/IntervalTranslation.lean、GMZP0/FiniteAverages.lean
- 四平移采样及实际序列平滑：GMZP0/FourShiftSmoothing.lean、GMZP0/CyclicSmoothing.lean
- 统一正平滑平均及四面相位：GMZP0/PositiveSmoothedAverage.lean、GMZP0/CubicFaces.lean
- 有限平均与单步盒式不等式：GMZP0/MeanAlgebra.lean、GMZP0/BoxCauchyStep.lean
- 面因子递归与完整盒式不等式：GMZP0/BoxFaces.lean、GMZP0/BoxMoment.lean
- 盒范数及实际四平移应用：GMZP0/BoxNorm.lean、GMZP0/CyclicBoxNorm.lean
- 全 lag 平均与正盒矩：GMZP0/FullLagAverage.lean、GMZP0/PositiveBoxAverage.lean
- 保留原响应的统一正盒矩：GMZP0/UniformBoxAverage.lean
- Boolean 共轭与完整顶点展开：GMZP0/CubeConjugation.lean、GMZP0/CubeExpansion.lean
- 圆周相位与原循环立方展开：GMZP0/CubePhaseAlgebra.lean、GMZP0/CyclicCubeExpansion.lean
- 循环重定根与十六因子分离：GMZP0/CyclicCubeReroot.lean、GMZP0/CyclicCubePhase.lean
- 统一正立方平均及 t 重排：GMZP0/UniformCubeAverage.lean、GMZP0/CyclicCubeTime.lean
- 全部非零权重顶点的原响应：GMZP0/OriginalCubeVertices.lean
- Weyl 提取前的统一加权平均：GMZP0/UniformWeightedTimeAverage.lean
- 线性指数和与任意区间逆估计：GMZP0/LinearWeyl.lean、GMZP0/IntervalWeyl.lean
- 精确降次平均、数量界及小尺度反例：GMZP0/WeylDifferencing.lean、GMZP0/WeylLargeCorrelations.lean
- 二次、三次相位与实际交叠：GMZP0/PolynomialDifferencing.lean
- 稠密回归的非零小倍数：GMZP0/AffineReturnSeed.lean
- 回归分组与定量放大：GMZP0/ReturnFiber.lean、GMZP0/AffineReturnAmplification.lean
- 统一仿射回归和二次逆估计：GMZP0/UniformAffineReturns.lean、GMZP0/QuadraticWeyl.lean
- 实际区间尺度转换：GMZP0/IntervalRescaling.lean、GMZP0/QuadraticIntervalWeyl.lean
- 实际成功分母分组与三次回归：GMZP0/DenominatorFiber.lean、GMZP0/CubicWeylReturns.lean
- 三次最高系数与共同分母：GMZP0/CubicWeyl.lean、GMZP0/CubicCommonDenominator.lean
- 原立方 Weyl 与保留权重的选择：GMZP0/OriginalCubeWeyl.lean、GMZP0/WeightedCubeWeyl.lean
- 原响应和统一正立方质量：GMZP0/UniformOriginalCubeCapture.lean
- Weyl 文献核查和后续精确接口：WEYL_SOURCE_AUDIT.md
- k 消去及正标签约化：GMZP0/CubeLagRemoval.lean、GMZP0/CubeSignSymmetry.lean、GMZP0/PositiveCubeAverage.lean
- 独立坐标与碰撞概率：GMZP0/CoordinateMean.lean、GMZP0/PairCollision.lean、GMZP0/CubeCollision.lean
- 碰撞条件反例：GMZP0/CollisionObstruction.lean
- 原加权去碰撞与统一阈值：GMZP0/WeightedCollisionRemoval.lean、GMZP0/UniformCollisionScale.lean
- 保留完整原响应的互异立方：GMZP0/UniformDistinctCubeCapture.lean
- 固定代表、格点误差及整数分支：GMZP0/LiftRounding.lean、GMZP0/LiftChoices.lean、GMZP0/CubeRounding.lean
- 局部修正及全局点指派：GMZP0/CubeLiftCorrection.lean、GMZP0/IndependentAssignments.lean、GMZP0/GlobalFiniteChoice.lean
- 循环原支持、成功概率及一次全局提升：GMZP0/CyclicLiftValues.lean、GMZP0/CyclicLiftProbability.lean、GMZP0/CyclicGlobalLift.lean
- 保留全部原响应的统一实提升：GMZP0/UniformOriginalRealLift.lean
- 已证全局实提升接口：REAL_LIFT_INTERFACE.md
- 完整频率网格及准确反例：GMZP0/FiniteCharacterOrthogonality.lean、GMZP0/FrequencyMesh.lean、GMZP0/FrequencyAliasing.lean
- 原局部范数及权重恒等式：GMZP0/LocalCubeNorm.lean、GMZP0/WeightedFrequencyCube.lean、GMZP0/CyclicFrequencyAverage.lean
- 统一局部四阶矩及原响应纤维：GMZP0/UniformOriginalLocalFour.lean、GMZP0/UniformOriginalLocalFibers.lean
- 已证精确频率平均与后续族拼接接口：FREQUENCY_AVERAGING_INTERFACE.md
- 公理核查：GMZP0/Audit.lean
- 机器检查输出：verification/build.log、verification/axioms.log、verification/result.json

运行 python verify.py 可重新执行构建与逐项公理核查；这一记录报告的是 Lean
证明检查结果，不使用数值测试或文件哈希代替一般数学证明。

- F18 有限傅里叶与差分密度：GMZP0/FiniteFourierEnergy.lean、GMZP0/LocalCubeDifference.lean、GMZP0/LocalFourierBound.lean

- F19 完整局部—全局比较：GMZP0/TwistedCube.lean、GMZP0/LocalGlobalComparison.lean；七阶权重恒等式：GMZP0/GlobalFrequencyAverage.lean

- F21 配对重数、异常配对和密度能量：GMZP0/PairRepresentations.lean、GMZP0/ExceptionalPairs.lean、GMZP0/PairDensity.lean
- F21 原响应到实七阶立方的条件性核心定理：GMZP0/PairSeventhMoment.lean、GMZP0/UniformOriginalRealSeven.lean
- 外部拼接输入的精确类型：GMZP0/ConcatenationInterface.lean；检查点说明：CORE_SEVEN_CUBE_CHECKPOINT.md
- F22 七阶立方准备：GMZP0/GlobalCubeCollision.lean、GMZP0/GlobalCubeThreshold.lean、GMZP0/PreparedSevenFibers.lean
- F22 原响应统一准备及原基点恢复：GMZP0/UniformPreparedSeven.lean、GMZP0/OriginalFiberRetention.lean
- 值模型前后核心接口：STRUCTURAL_VALUE_INTERFACE.md
- F23 有限 Schur 和完整块估计：GMZP0/FiniteSchur.lean、GMZP0/BlockSchur.lean
- F23 大块计数与原小弧接口：GMZP0/FewLargeBlocks.lean、GMZP0/OriginalBlockSchur.lean
- 精确作用域与平方根反例：FINITE_BLOCK_SCHUR_INTERFACE.md
- F24 原算子误差和逐点指派：GMZP0/OperatorStability.lean、GMZP0/AssignedOperator.lean
- F24 精确能量合并与主弧传递：GMZP0/FiniteEnergyTriangle.lean、GMZP0/MajorArcStability.lean
- F24 条件性冻结单步：GMZP0/FreezingStep.lean；说明：FREEZING_STEP_INTERFACE.md
- F25 原边界和精确块压缩：GMZP0/WideVertical.lean、GMZP0/WideBlock.lean
- F25 完整相位与大块估计：GMZP0/WideGram.lean、GMZP0/WideLagBounds.lean
- F25 实际大块的非零位移和原根：GMZP0/LargeBlockLags.lean；说明：WIDE_BLOCK_INTERFACE.md
- F26 实际区间三次 Weyl 与线性相位：GMZP0/CubicIntervalWeyl.lean、GMZP0/AffineBlockPhase.lean
- F26 保留分母的返回和正反块关系：GMZP0/PowerAffineReturns.lean、GMZP0/AffineBlockRelations.lean
- F26 斜率关系、真实计数和算子：GMZP0/AffineTopRelation.lean、GMZP0/AffineNoRelation.lean
- F26 精确作用域：AFFINE_FREEZING_INTERFACE.md；下一步：ORDINARY_FREEZING_PROOF_PLAN.md
- F27 圆周网格和实际子模型：GMZP0/CircleGrid.lean、GMZP0/AffineChildren.lean
- F27 线性冻结的次数零归约：GMZP0/AffineFreezing.lean；作用域：AFFINE_CHILD_INTERFACE.md
- F27 下一核心目标：CONSTANT_FREEZING_PROOF_PLAN.md
- F28 精确 Fourier 分解、循环原输入与原响应：GMZP0/FourierTranslation.lean、GMZP0/CyclicInput.lean、GMZP0/ConstantFourier.lean
- F28 已证范围与剩余横向核心：CONSTANT_FOURIER_INTERFACE.md
- F29 横向核、相位、Schur 和条件性冻结：GMZP0/HorizontalCubicKernel.lean、GMZP0/ConstantGramPhase.lean、GMZP0/HorizontalSchur.lean、GMZP0/ConstantFreezing.lean
- F29 外部输入边界及剩余高次核心：CONSTANT_FREEZING_INTERFACE.md
- F30 真正的高次模型、完整相位及单块返回：GMZP0/OrdinaryPolynomialAlgebra.lean、GMZP0/OrdinaryProfiles.lean、GMZP0/OrdinaryBlockRelations.lean
- F30 精确作用域与非线性返回缺口：ORDINARY_BLOCK_INTERFACE.md
- F31 实际低次多项式及全根子模型：GMZP0/OrdinaryChildren.lean
- F31 未证明的内部返回契约与已证分母适配：GMZP0/MonomialReturnInterface.lean
- F31 条件性顶次关系、原算子与次数归纳：GMZP0/OrdinaryTopRelation.lean、GMZP0/OrdinaryFreezing.lean
- F31 精确作用域与下一核心目标：ORDINARY_DESCENT_INTERFACE.md、MONOMIAL_RETURNS_PROOF_PLAN.md
- F32 与中心无关的整数插值与实际短簇：GMZP0/MonomialInterpolation.lean、GMZP0/MonomialSeed.lean
- F32 全次数误差加强与完整返回证明：GMZP0/MonomialAmplification.lean、GMZP0/MonomialReturns.lean
- F32 普通多项式冻结的完成边界：MONOMIAL_RETURNS_INTERFACE.md
