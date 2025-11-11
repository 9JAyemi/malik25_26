// SVA for calculator – focused, high-quality checks and coverage.
// Bind this file to the DUT.
// - Confirms pipeline capture, operation semantics, outputs mapping, and error behavior.
// - Uses both internal-reg-based and port-based assertions for strong end-to-end checking.
// - Includes concise coverage for all ops and div-by-zero.

module calculator_sva (
  input  logic         clk,
  input  logic         reset_n,

  // DUT ports
  input  logic [31:0]  A,
  input  logic [31:0]  B,
  input  logic [1:0]   control,
  input  logic         start,
  input  logic [31:0]  C,
  input  logic         error,

  // DUT internals
  input  logic [31:0]  C_reg,
  input  logic [31:0]  A_reg,
  input  logic [31:0]  B_reg,
  input  logic [1:0]   control_reg,
  input  logic         start_reg,
  input  logic [31:0]  result_reg,
  input  logic         error_reg
);

  // Helper function: DUT operation
  function automatic logic [31:0] f_op (logic [31:0] a, logic [31:0] b, logic [1:0] ctrl);
    case (ctrl)
      2'h0: f_op = a + b;
      2'h1: f_op = a - b;
      2'h2: f_op = a * b;
      2'h3: f_op = (b == 0) ? 32'h0 : (a / b);
    endcase
  endfunction

  // Reset behavior (async active-low)
  assert property (@(posedge clk)
    !reset_n |-> (C==32'h0 && error==1'b0 &&
                  C_reg==32'h0 && A_reg==32'h0 && B_reg==32'h0 &&
                  control_reg==2'h0 && start_reg==1'b0 && error_reg==1'b0))
    else $error("Reset state incorrect");

  // 1) Register capture from ports (1-cycle latency)
  assert property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n) |-> (A_reg==$past(A) && B_reg==$past(B) &&
                        control_reg==$past(control) && start_reg==$past(start)))
    else $error("Input capture to *_reg incorrect");

  // 2) Result computation from previous cycle's regs
  assert property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n) |-> result_reg == f_op($past(A_reg), $past(B_reg), $past(control_reg)))
    else $error("result_reg computation mismatch");

  // 3) error_reg driven only by div-by-zero of previous regs
  assert property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n) |-> error_reg == (($past(control_reg)==2'h3) && ($past(B_reg)==32'h0)))
    else $error("error_reg mismatch");

  // 4) Output mapping from internals (C is 1-cycle behind result_reg; error mirrors error_reg)
  assert property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n) |-> C == $past(result_reg))
    else $error("C pipeline mapping mismatch");

  assert property (@(posedge clk) disable iff (!reset_n)
    error == error_reg)
    else $error("error output not mirroring error_reg");

  // 5) End-to-end functional check from external ports (2-cycle latency)
  assert property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n,2) |-> C == f_op($past(A,2), $past(B,2), $past(control,2)))
    else $error("End-to-end C functional mismatch from ports");

  // 6) End-to-end error timing from external ports (1-cycle latency)
  assert property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n) |-> (error == (($past(control)==2'h3) && ($past(B)==32'h0))))
    else $error("End-to-end error timing mismatch from ports");

  // 7) Correlate error with next-cycle C for div-by-zero
  assert property (@(posedge clk) disable iff (!reset_n)
    error |-> ##1 (C==32'h0))
    else $error("Div-by-zero: C not zero in next cycle");

  // Coverage: exercise each op, div-by-zero path, and non-zero divide
  cover property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n,2) && ($past(control,2)==2'h0) && (C == ($past(A,2)+$past(B,2))));
  cover property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n,2) && ($past(control,2)==2'h1) && (C == ($past(A,2)-$past(B,2))));
  cover property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n,2) && ($past(control,2)==2'h2) && (C == ($past(A,2)*$past(B,2))));
  cover property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n) && ($past(control)==2'h3) && ($past(B)==32'h0) && error ##1 (C==32'h0));
  cover property (@(posedge clk) disable iff (!reset_n)
    $past(reset_n,2) && ($past(control,2)==2'h3) && ($past(B,2)!=32'h0) &&
    (C == ($past(A,2)/$past(B,2))));

  // Cover start activity (unused by functionality, but sampled)
  cover property (@(posedge clk) disable iff (!reset_n) $changed(start));

endmodule

bind calculator calculator_sva calc_sva_bind (.*);