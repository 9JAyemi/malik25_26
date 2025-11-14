// SVA for adder_subtractor
module adder_subtractor_sva (
  input logic        clk,
  input logic [3:0]  A, B,
  input logic        mode,
  input logic [3:0]  Q,

  // internal regs (bound hierarchically)
  input logic [3:0]  A_reg, B_reg, Q_reg,
  input logic        mode_reg
);

  default clocking cb @(posedge clk); endclocking

  // past-valid guard for $past-based checks
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // 1) Output mirrors registered result
  assert property (Q == Q_reg)
    else $error("Q must mirror Q_reg");

  // 2) One-cycle functional latency from inputs (black-box check)
  assert property (mode == 1'b0 |=> Q == (A + B))
    else $error("Add mode incorrect (1-cycle latency)");
  assert property (mode == 1'b1 |=> Q == (A - B))
    else $error("Sub mode incorrect (1-cycle latency)");

  // 3) Inputs are registered (structural intent)
  assert property (disable iff (!past_valid) A_reg == $past(A))
    else $error("A not properly registered");
  assert property (disable iff (!past_valid) B_reg == $past(B))
    else $error("B not properly registered");
  assert property (disable iff (!past_valid) mode_reg == $past(mode))
    else $error("mode not properly registered");

  // 4) Registered arithmetic uses prior registered operands (internal check)
  assert property (disable iff (!past_valid)
                   Q_reg == ($past(mode_reg) ? ($past(A_reg) - $past(B_reg))
                                             : ($past(A_reg) + $past(B_reg))))
    else $error("Q_reg incorrect vs registered operands");

  // Coverage: both ops, overflow/underflow, and back-to-back mode toggle
  cover property (mode == 1'b0 |=> Q == (A + B));             // addition used
  cover property (mode == 1'b1 |=> Q == (A - B));             // subtraction used
  cover property ((mode == 1'b0 && ({1'b0,A}+{1'b0,B})[4]) ##1 (Q == (A + B))); // add overflow
  cover property ((mode == 1'b1 && (A < B))               ##1 (Q == (A - B))); // sub underflow
  cover property ((mode==1'b0) ##1 (Q==(A+B)) ##1 (mode==1'b1) ##1 (Q==(A-B))); // toggle sequence

endmodule

// Bind into DUT
bind adder_subtractor adder_subtractor_sva
  (.clk(clk),
   .A(A), .B(B), .mode(mode), .Q(Q),
   .A_reg(A_reg), .B_reg(B_reg), .Q_reg(Q_reg), .mode_reg(mode_reg));