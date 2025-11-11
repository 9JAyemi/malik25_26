// SystemVerilog Assertions (SVA) for the given design

// SVA bound to sequential_multiplier
module sequential_multiplier_sva (
  input logic        clk,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [15:0] P,
  input logic [15:0] temp_P
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // 1-cycle latency and functional correctness
  assert property (@(posedge clk) past_valid |-> P == $past(A*B));

  // P mirrors internal register
  assert property (@(posedge clk) P == temp_P);

  // Minimal coverage
  cover property (@(posedge clk) past_valid && P != $past(P));
  cover property (@(posedge clk) (A==8'h00 || B==8'h00));
  cover property (@(posedge clk) (A==8'hFF && B==8'hFF));
endmodule

bind sequential_multiplier sequential_multiplier_sva u_mult_sva (
  .clk(clk), .A(A), .B(B), .P(P), .temp_P(temp_P)
);


// SVA bound to top_module (covers comparator + top wiring + product behavior with reset)
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic [15:0] P,
  input logic        out,
  input logic        eq,
  input logic        gt_a,
  input logic        gt_b
);
  logic past_valid;
  always @(posedge clk or posedge reset)
    if (reset) past_valid <= 1'b0; else past_valid <= 1'b1;

  // Multiplier functional latency (reset-aware)
  assert property (@(posedge clk) disable iff (reset) past_valid |-> P == $past(A*B));

  // Comparator correctness
  assert property (@(posedge clk) disable iff (reset) (eq   == (a==b)));
  assert property (@(posedge clk) disable iff (reset) (gt_a == (a>b)));
  assert property (@(posedge clk) disable iff (reset) (gt_b == (b>a)));
  assert property (@(posedge clk) disable iff (reset) $onehot({eq,gt_a,gt_b}));

  // Top-level output function
  assert property (@(posedge clk) disable iff (reset) out == (eq | gt_a));

  // No X/Z on observed outputs after reset deassert
  assert property (@(posedge clk) disable iff (reset) !$isunknown({P,out,eq,gt_a,gt_b}));

  // Coverage: exercise all comparator outcomes and interesting multiplies
  cover property (@(posedge clk) disable iff (reset) (a==b) &&  eq);
  cover property (@(posedge clk) disable iff (reset) (a>b)  &&  gt_a);
  cover property (@(posedge clk) disable iff (reset) (b>a)  &&  gt_b);
  cover property (@(posedge clk) disable iff (reset) (A==8'h00 || B==8'h00));
  cover property (@(posedge clk) disable iff (reset) (A==8'hFF && B==8'hFF));
  cover property (@(posedge clk) disable iff (reset) (A==8'h80 && B==8'h80));
  cover property (@(posedge clk) disable iff (reset) past_valid && P != $past(P));
endmodule

bind top_module top_module_sva u_top_sva (
  .clk(clk), .reset(reset),
  .A(A), .B(B), .a(a), .b(b),
  .P(P), .out(out),
  .eq(eq), .gt_a(gt_a), .gt_b(gt_b)
);