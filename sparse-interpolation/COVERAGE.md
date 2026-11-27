# 最终 TeX 数学主张与 Lean 对照

核对对象为 [paper/Grenet.tex](paper/Grenet.tex)。节号按最终 TeX 的定理和章节编号。下表把明确的数学主张、用作证明的中间结论，以及例子逐项对照到项目声明。数学库中的基本代数、有限组合及微积分引理均通过固定版本 Mathlib 导入。背景与引文不作为本稿的算法结论。全工程复放及公理审计见[重放日志](verification/lean-replay.txt)。

| TeX 位置 | 数学主张 | Lean 声明和依赖核对 |
| --- | --- | --- |
| 摘要、§1 定理 1.1 上界 | 每个非零、加法无整数挠的含幺交换环，每个正则步长和每个起点，同环精确值的 \(4t\) 前缀辨识至多 \(t\) 项正式多项式。没有次数限制 | `GrenetPaper.four_t_samples`、`four_t_worst_case`。完整依赖 `GrenetRankComplete.finset_full_minor`、`GrenetResidue.normalized_odd_part` 和 `Round4Transfer.determinesUnboundedSparse_of_symbolic_unit_ideals`。有限支持补齐在内部处理，无外加 rank 或子式条件。 |
| 摘要、§1 定理 1.1 下界 | 固定同一个 \(R,b,t\) 后，存在共同起点令每个 \(m<4t\) 的前缀失败 | `GrenetPaper.four_t_worst_case`、`regular_step_prefix_not_determining`。量词顺序为先给定 \(R,b,t\)，再选一个起点，对全部 \(m<4t\) 成立。 |
| 摘要、§1 定理 1.2 | \(Ba=Ab\)、\(B>0\)、\(t\ge1\)、\(b\) 正则时，任意长度 \(m\) 成功 iff 达到给定闭式阈值 | `GrenetRational.rational_ratio_exact_manuscript` 和 `rational_ratio_least`。阈值输入为约分后的 \(z=A/B\)，定理容许更一般的未约分 \(A,B\)。原稿互素假设由此覆盖。 |
| §1 定理 1.2 同号表述 | 整数和半整数时，以每个前缀 \(2t\) 个严格同号点为条件。零点不计入两类 | `GrenetHalf.rational_half_prefix_iff`，与 `GrenetRational.den_le_two_iff_double_integer`、`posIndices_card`、`negIndices_card`、`half_prefix_exact` 组合。 |
| §1 通用前缀与可选正有理起点 | 正有理归一化起点只需 \(2t\)。统一最坏值按所有起点取量词 | `GrenetRational.threshold_of_positive` 与 `rational_ratio_exact`，以及 `GrenetPaper.four_t_worst_case`。 |
| §1 退化情形 | 整数挠可能造成正式多项式的函数碰撞，零步长不能统一辨识 | `GrenetRational.characteristic_two_collision`、`zero_step_collision`。 |
| §2 支持矩阵、求差与补零 | 支持差至多 \(2t\)，可反向拆成两份；零指数在零节点仍取 \(1\)；任意小支持可补齐 | `evaluationMatrix`、`evaluationMatrix_mulVec`、`admissible_sub`、`admissible_iff_split`、`determinesSparse_iff_max_support_matrices`、`GrenetRational.determines_iff_supports`。 |
| §2 无共同根与单位理想 | 任意代数闭域扩张中的逐点子式非零给出符号单位理想 | `Round4Transfer.polynomial_span_eq_top_iff_no_common_root`、`symbolic_fullMinorIdeal_eq_top_of_no_common_root`。覆盖零理想及任意有限指数集，无需固定同一个子式。 |
| §2 局部化、列缩放、伴随消去 | 非零整数及步长在单射局部化中可逆，由单位子式理想下降到 \(R\) | `progression_injective_of_embedding`、`progression_injective_of_symbolic_unit_ideal`、`map_fullMinorIdeal`、`injective_of_fullMinorIdeal_eq_top`，伴随步骤由 McCoy 的 `kernel_coordinate_kills_full_minors` 提供。 |
| §2 引理 2.1 同号节点 | 任意非负互异指数，方阵对应互异同号节点非奇异。实多项式的严格正根数小于非零项数 | `GrenetSameSign.card_lt_support_of_positive_roots`、`det_pow_ne_zero_real`、`det_pow_ne_zero_rat`。Rolle 归纳及 \(X\mapsto-X\) 的列符号归约在同一依赖中。 |
| §3.1 差分化简与有限截断 | 写出 \(P_j\) 的系数式，有限截断正确，换基对角为 1，取出 \(c^{\binom{k}{2}}\) | `SharpDifference.rowPoly_finite`、`fwdDiff_binomial`、`fwdDiff_rowPoly`、`det_differenceMatrix`、`determinant_row_factor`。 |
| §3.1 整性与符号 Vandermonde | \(v_2(r!)\le r-1\)，在实际局部环中先除交错因子后代入，商对称；模 2 只依赖奇指数计数 | `factorial_val_two_le`、`scaled_factorial_mem`、`symbolicV_dvd_alternant`、`exists_symmetric_alternant_quotient`、`common_symbolic_normalization`、`GrenetResidue.normalized_same_odd_count`。比较使用共同截断。 |
| §3.1、§5 剩余域的识别 | 二进局部系数环模 2 是 (mathbb F_2)；任意素数 (p) 时，有理局部环按分母不被 (p) 整除刻画，其剩余域是 (mathbb F_p) | `SharpDifference.mem_localTwo_iff_odd_den`、`GrenetPaper.parity_residue_field`、`strict_localization_denominator`、`strict_residue_field`。给出实际环同构，等式的剩余环与正文一致。 |
| §3.1 归一化常数项 | 在零处降阶乘变为首一三角基，\(N_E(0)=1\) | `SharpDifference.localRowMatrix_det_atZero`、`normalized_atZero`、`GrenetResidue.normalized_at_zero`。 |
| §3.2 对称行及重数 | 对称配对造成奇偶列限制和秩亏；每个中心精确保证所写的因子整除下界，各中心因子可合乘 | `SharpFactor.opposite_powers_rank_deficiency`、`pow_X_sub_C_dvd_det_of_rank`、`halfSample_factor`、`GrenetResidue.factor_dvd_normalized`、`all_factors_dvd`。归一化中分母与该因子互素。 |
| §3.2 配对计数 | 奇中心阶梯与偶中心阶梯，亏数和分别为 \(m^2\)、\(m(m-1)\)，极端空区间允许 | `HalfBlockCount.pairs_as_interval`、`first_odd`、`second_odd`、`first_even`、`second_even`、`odd_multiplicity`、`even_multiplicity`。 |
| §3.3 最小代表、度数饱和与奇偶交换 | 对应指数代表的次数预算，代表变成完整因子积，平移 1 不改约化 | `GrenetResidue.representative_injective`、`representative_sum`、`representative_factor_exact`、`normalized_shift_one_residue`、`normalized_residue`。 |
| §3.3 局部环奇因子和剩余商 | \(N=F A\)，奇因子首项系数为单位，\(\bar A=1\)，中心乘积的多余尾项指数为零 | `oddFactors_unit_leadingCoeff`、`normalized_odd_dvd`、`normalized_odd_part`、`multiplicity_zero_of_large`。 |
| §4 反射、多项式恒等式 | 不仅在非零 \(Z\) 上成立。实际偶半块是归一化倒数；余式用真实 \(d=\sum e_i-\binom{2t}{2}-m^2\) | `GrenetPaper.reflect_source_det` 和 `evenPolynomialMatrix_factor` 对应实际符号矩阵及显式乘积。度数和首一性来自 `GrenetRankArendt.normalized_residual_budget`、`GrenetRankAlgebra.reflect_monic_degree`。 |
| §4 两个余式互素及显式异常 | 约化为 \(Z^d\)、\((Z+1)^d\)，首一公因子下沉，两半块共同零点只能落在显式奇中心或其平移处 | `GrenetRankArendt.normalized_residual_reductions`、`GrenetRankAlgebra.isCoprime_reflect_shift`、`GrenetPaper.even_and_odd_common_root`。 |
| §4 整点排除与全列秩 | 整点 \(2k\) 行有 \(k\) 个严格同号节点，从有限支持得真正满列子式，并完成原环结论 | `GrenetRank.rational_prefix_minor`、`full_minor_of_normalized_half`、`GrenetRankComplete.finset_full_minor`、`GrenetPaper.four_t_full_minor`。 |
| §4 整数见证 | \(W=X\prod_{\nu=1}^n(X^2-\nu^2)\)，有 \(n+1\) 个非零项，根集正是 \([-n,n]\) 的整数，根数含重数等于次数 | `Round4Prefix.symmetricWitness_eq_product`、`symmetricWitness_support_card`、`symmetricWitness_root_set`、`symmetricWitness_natDegree`、`symmetricWitness_root_count`。 |
| §4 原环见证和下一点 | \(W_b\) 的实际乘积与按次数齐次化的系数相同，支持保留，前缀碰撞、下一点区分，拆成恰好 \(t\) 项的两份 | `GrenetPaper.scaledWitness_eq_product`、Mathlib `Polynomial.coeff_scaleRoots`、`scaledWitness_support`、`scaledWitness_eval`、`regular_step_collision`。无需 \(b\) 为单位。 |
| §5 低于 \(k\) 的下界、清分母 | 有理线性系统行少于列有核；原环统一清分母和齐次变形后保留支持与零观测 | `GrenetMcCoy.exists_kernel_of_fewer_rows`、`GrenetRational.normalized_prefix_basic_lower`、`rational_kernel_clearing`。非零见证由支持等式保留，原环 eval 精确为零。 |
| §5 两个方向的逐列传递 | \(B(a+ib)=b(A+Bi)\)、\(B(z+i)=A+Bi\)，正规化前后对每个支持同为单射或同为非单射 | `GrenetRational.scaled_evaluation_iff`、`integer_nodes_iff`、`rational_ratio_support_iff`、`rational_ratio_prefix_iff`。上、下两个方向均保持原环量词。 |
| §5 严格局部条件 | 约分分母大于 2 时，存在奇素数分母因子，或分母含 4。两种情况下逆起点严格满足 \(p\) 进阈值 | `GrenetStrict.denominator_prime`、`inverse_val_of_dvd_den`、`exists_strict_prime_of_den`。用整数乘法形式表达 \((p-1)v_p(c)>1\)。 |
| §5 严格归一化行列式 | 任意 \(p\)、严格局部步长，阶乘界、差分化、正规化后模 \(p\) 为 1，故每个不同指数集合对应 \(k\) 行足够 | `GrenetStrict.factorial_bound`、`kernel_reduce`、`fwdDiff_row`、`strict_symbolic_quotient`、`determinant_row_factor`、`strict_normalized_residue_one`、`prefix_det_ne_zero_of_den_gt_two`。 |
| §5 半整数对称和碰撞 | 两边绝对值集合嵌套，非零绝对值数等于较大符号计数。小于 \(k\) 时平方多项式在全部节点消失 | `GrenetHalf.doubleNode_reflect_side`、`card_nonzeroAbs_of_reflect_side`、`rational_progression_card_nonzeroAbs`、`rational_half_prefix_iff`。实际平方见证和支持上界由 `GrenetPaper.not_determining_of_small_squared_sample_set` 核验；反向用同号子式。 |
| §5 floor/ceiling、例子、负步长 | 明确 \(q,p\) 及所有分支，例子 \(t=1,2\)，负实际步长按归一化起点处理 | `GrenetRational.negIndices_card`、`posIndices_card`、`signThreshold_le_iff`、`rational_ratio_exact_manuscript`、`rational_progression_exact`、`threshold_one_eq`、`published_threshold_examples`。 |
| RATIONAL.md 补充 | 唯一达到 \(4t\) 的有理归一化起点，及零稀疏度约定 | `GrenetRational.threshold_eq_four_t_iff`；零输入的唯一性见定理 1.1 上界的 \(t=0\) 实例，空前缀为其直接实例。 |
| 附录 A 极端列数 | 空列子式理想为单位理想；列多于行时该理想为零 | `GrenetRational.fullMinorIdeal_empty_columns`、`fullMinorIdeal_fewer_rows`。前者接受空行，后者有限行列。 |
| 附录 A McCoy 引理 | 有限矩阵的核为零 iff 极大列子式公共湮灭子为零；极大未被杀死子式构造带符号余因子核 | `GrenetMcCoy.mulVec_injective_iff_fullMinorIdeal_annihilator_eq_bot`、`exists_kernel_of_kills_full_minors`。一般交换环，允许零因子。 |
| 附录 A 至多次数 | 检查所有基数 \(\min(2t,d+1)\) 的候选支持，允许重复节点 | `GrenetMcCoy.determinesSparse_iff_determinantal_annihilator`。次数和项数均为上界，采样函数无需单射。 |
| 附录 A 恰好次数、固定首项 | 最大低阶支持大小 \(\min(2(t-1),d)\)，不用顶次列 | `determinesFixedLeading_iff_determinesLower`、`determinesFixedLeading_iff_determinantal_annihilator`。首系数非零，保留 \(t\ge1\)。 |
| 附录 A 恰好次数、可变首项 | 至少有第三元素时附加顶次列，可用两个非零系数实现任意顶次差 | `exists_nonzero_sub_eq`、`determinesExactDegree_iff_support_matrices`、`determinesExactDegree_iff_determinantal_annihilator`，原有第三元素条件明确保留。 |
| 附录 A 二元恰好次数 | 非零首项固定为 1，差仅在低次用 \(t-1\) | `determinesExactDegree_zmodTwo_iff_fixed`、`determinesExactDegree_zmodTwo_iff_determinantal_annihilator`。 |
| 附录 A 恰好项数、第三元素 | 足够的允许位置时可实际拆分至多 \(2t\) 项的差为两个恰好 \(t\) 项输入。恰好次数的拆分先处理 \(t-1\) 个低阶项 | `exact_support_difference_of_third`、`determinesExactDegreeExactTermsWith_iff`、`determinesBoundedDegreeExactTerms_iff_determinesSparse`，总允许位置与顶次假设均在接口中。 |
| 附录 A 二元恰好项数 | 二元支持对称差精确为偶数大小且至多 \(2\min(t,N-t)\)，增广全 1 行检测该偶性，恰好次数时在低阶应用 | `zmodTwo_exact_support_difference_iff`、`determinesExactDegreeExactTerms_zmodTwo_iff_even_kernel`、`determinesExactDegreeExactTerms_zmodTwo_iff_determinantal_annihilator`、`determinesBoundedDegreeExactTerms_zmodTwo_iff_determinantal_annihilator`。 |

§6 的前人工作比较与附录 B 的 AI 披露不是数学命题。稿件没有声称有效解码算法或复杂度上界。复现脚本中的阈值计算属于闭式公式的实现，Python 有限枚举只记为回归。
