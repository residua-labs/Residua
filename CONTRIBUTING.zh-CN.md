# 贡献指南

[English](CONTRIBUTING.md) | 中文

感谢你对 Residua 的关注。

## 开发如何进行

Residua 由项目团队在私有工作区开发；本公开仓库是每个版本的发布源。
日常开发、代码评审与审计轨迹不在此进行，因此 pull request 无法直接合入。

## 你可以做的

- **开 issue**：bug、文档不清、验证文档中的错误断言、特性请求。
  尤其欢迎在我们未尝试过的机器上复现 seed 配方——请附上宿主信息
  （`uname -a`、编译器版本）与结果。
- **在 issue 中提议修改**：说明改动与理由，维护者接手。小修
  （错别字、死链、错误摘要）常被原样带进下一版本。
- **私密报告漏洞**——绝不在公开 issue 中报告。见
  [SECURITY.md](SECURITY.md)。

## 构建与测试

- 从提交的 seed 重建编译器：`bootstrap/seed/*/README.md` 中的配方，
  支持 Linux x86-64。
- 校验整个版本：`docs/VERIFY-RELEASE.md`。
- 运行随附的测试与基准套件：`TESTING.md`。

## 风格

`.rsd` 源码使用语言的自举子集（`docs/LANGUAGE.md`）。公开文本遵循
`release/TERMS.tsv`——内部名称不进入公开文档；真实技术术语在
`docs/GLOSSARY.zh-CN.md` 中定义一次。

## 行为准则

参与受 [行为准则](CODE_OF_CONDUCT.md) 约束。
