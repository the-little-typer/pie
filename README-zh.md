# Pie: 一種依賴類型的小語言

這是Pie, Daniel P. Friedman 和 David Thrane Christiansen 寫的 _The Little Typer_的伴侶語言。

## 如何使用Pie

Pie 是一個 [Racket](http://racket-lang.org) 語言, 要求 Racket version 6.5 以上。安裝之後，Racket 將解釋任何以 `#lang pie` 開頭的文件爲 Pie 程式。

### 待辦清單

如果你無法弄清楚要在 Pie 程式中的某些地方寫什麼，可以留下一個空間以待稍後填寫。這對應於_The Little Typer_中的空盒子。這些在 Pie 中寫成 `TODO` 。

### DrRacket 整合

Pie 為 DrRacket 提供了附加信息，包括工具提示和其他元數據。 將鼠標指向一對括號，名稱或Pie構造函數或類型構造函數，以查看有關表達式的信息。

此外，Pie 支持 [DrRacket TODO list](https://github.com/david-christiansen/todo-list) 。

### 命令行讀取﹣求值﹣輸出循環

如果您更喜歡 DrRacket 以外的編輯器，可以在命令行上啟動 Pie 讀取﹣求值﹣輸出循環。 為此，請使用指令 `racket -l pie -i` 以交互模式使用 `pie` 語言啟動 Racket。


## 安裝說明
Pie 可從 Racket 包服務器安裝。 如果您不打算對 Pie 進行自己的更改，那麼從那里安裝它是最簡單的。

### 從 DrRacket

點擊"文件"，"Install Package..."。在框輸入`pie` 然後點擊"Install"。

### 從命令行

執行以下命令
`raco pkg install pie`

## 更新

因為它是爲了支援一本書，所以Pie語言已經完成，不會改變。 但是，Pie的這個實現可能有一天會獲得額外的功能，或者它可能需要更新才能跟上新計算機的步伐。 在這種情況下，請像任何 Racket 包一樣更新它。

### 從 DrRacket

點擊"文件"，"Install Package..."。在框輸入`pie` 然後點擊"Update"。

### 從命令行

執行以下命令
`raco pkg update pie`
