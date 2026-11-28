# 五篇公开论文：Lean 补证与复现

公开 Lean 基线为 [95ad3fb](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/tree/95ad3fb52aeac8376ba835b76987ef5f9d6156d6)。第 2 篇 [5a1bbd6](https://github.com/dch-and-Elara/some-research-inspired-by-openais-eth-preprint/commit/5a1bbd6f48e111e59c380bb679a944fb6fdc3d43) 只明确了论文定理 6 的平衡布局前提，未改变任何 Lean 源。本目录是对公开项目的增量，不修改原论文或原证明。

| 篇 | 补证 | 新模块／具名公理检查 |
|---|---|---:|
| 1 | 任意删点集的式 (18)；原 §6.1 评值核、像、逐阶维数；γ=10；原区间和周期构造 (9)、(11)、(12)，同一周期集的尾部、预算和尖锐间距；原三值 Walsh 矩阵与插值矩阵同一方案；原 §7 约束空间及虚端点 | 13 / 89 |
| 2 | 实际测量块的式 (9)；原 (H_j,I_j) 的滤过、(XI_{j-1}) 核与逐阶坐标约束；按论文原路线推出式 (7) | 8 / 42 |
| 3 | 原样 Walsh 编码和恢复、精确秩 (2q+2)；同一 Gaussian/Bareiss 运行输出全部系数，并按实际位操作、表访问与控制付费 | 7 / 44 |
| 4 | 逐发生收费、外部数字轨迹的条件性收费转移；任意正确余数 lift；同一有序边表和 pin 计算上的扫描、清分母与位费用 | 9 / 27 |
| 5 | 任意合格物理布局的统一阈值、逐输入访问下界、同一根议程的积分提升与精确计数余数；精度反例、商环最小宽度、实际有限代数例子、行列式及子式反例；原 §6 实验脚本与逐字节一致的标准输出 | 10 / 22 |

合计 47 个新 Lean 模块、224 项具名公理检查。第 2 篇的整组独立重放另从源码重编 5 个原发表 Lean 模块、另有 5 项检查；未计入新增合计。第 1 篇使用 Lean 4.28，其余使用 Lean 4.24。各篇目录包含已重放的 Lean 源和覆盖说明；下面列出重放所用的上游。只用 Lean 标准公理；不分发预编译证明对象。

## 计费和覆盖边界

- 第 2 篇附录 A.2 的线性计费是给定合法边表的字记录操作，不是线性图灵机位时间。
- 第 3 篇总费用针对明示的有限稠密表和位操作模型，不声称通用机器模拟，也不声称和旧费用常数相等。
- 第 4 篇外部费用转移要求调用方给出保序单射，且像位置逐一付费；没有声称任意外部程序自动满足这些条件。§7 是声明的位费用模型，不是墙钟；A/B 的备选证明路线单列，已有形式化证明的数学结论不因此失效。
- 第 5 篇确证的是同一根议程与访问数，不是位时间。MSS 图族存在性和 OpenAI 固定密度位时间上界照原文保留外部引用。MAIN 原 TeX 到完整按位计费程序的抽取列为后续工作，§8 的上界也不包含未声明的预处理成本。没有加入新公理把这些外部结果当作 Lean 证明。

各份现有论文已经有证明的数学结论，不因省略另一条等价引理名或备选推导而计作未证。总数只计本次新增的模块和具名检查，不是论文实体定理的总数。


## Replaying the supplements

Each numbered folder is a separate overlay, not a replacement for an existing
Lake project. First build the corresponding baseline from this repository
using its committed toolchain and dependency pins. The current project roots are [boolean-cube](../../boolean-cube/) for Paper 1, [shared/reconstruction/formal](../reconstruction/formal/) for Papers 2–3, [root-separation/formal](../../root-separation/formal/) for Paper 4 and [rank-budget-barriers/formal](../../rank-budget-barriers/formal/) for Paper 5. Supplements live in each paper directory.
In a new output directory on Lean's module search path, compile the overlay
files in their local import order, treating warnings as errors. Paper 5's
P5OverlayPinnedSqZeroLib is a vendored support module from the pinned Mathlib;
its license is included, and it is not in the authored-module count. The
existing PDF and TeX files have not changed. SHA256SUMS.txt lists the exact
published Lean source bytes.

SHA256SUMS.txt is the historical receipt for the original supplement bundle, using its original paths. The Lean sources themselves live in their respective paper directories today.
