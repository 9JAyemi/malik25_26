// SVA for top_module
module top_module_sva (
  input logic        clk,
  input logic        reset_n,
  input logic [7:0]  in,
  input logic [7:0]  in_reg,
  input logic [15:0] sum,
  input logic [7:0]  out_vec,
  input logic [15:0] out
);

  default clocking @(posedge clk); endclocking

  // Reset behavior: clear register; outputs zero after NBA
  assert property (!reset_n |-> (in_reg==8'h00) ##0 (sum==16'h0000 && out==16'h0000));

  // Sequential capture: in_reg gets previous-cycle 'in' when out of reset
  assert property ((reset_n && $past(reset_n)) |-> (in_reg == $past(in)));

  // Combinational wiring checks (post-NBA)
  assert property (1'b1 |-> ##0 (out_vec == in_reg));
  assert property (1'b1 |-> ##0 (sum == ({8'h00, in_reg} + {in_reg, 8'h00})));
  assert property (1'b1 |-> ##0 (out == sum));

  // End-to-end functional latency: out equals 257 * previous-cycle input
  assert property ((reset_n && $past(reset_n)) |-> ##0 (out == (($past(in) << 8) + $past(in))));

  // No Xs during normal operation
  assert property (reset_n |-> !$isunknown({in_reg, sum, out}));

  // Coverage
  cover property (!reset_n ##1 reset_n);                     // reset release
  cover property ((reset_n && $past(reset_n) && $past(in)==8'h00) ##0 (out==16'h0000));
  cover property ((reset_n && $past(reset_n) && $past(in)==8'h01) ##0 (out==16'h0101));
  cover property ((reset_n && $past(reset_n) && $past(in)==8'hFF) ##0 (out==16'hFFFF));
  cover property ((reset_n && $past(reset_n) && $changed(in))); // exercise input changes

endmodule

bind top_module top_module_sva sva_i (
  .clk(clk),
  .reset_n(reset_n),
  .in(in),
  .in_reg(in_reg),
  .sum(sum),
  .out_vec(out_vec),
  .out(out)
);