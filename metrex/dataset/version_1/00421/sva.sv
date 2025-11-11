// SVA for accu: concise, quality-focused checks and coverage
`ifndef ACCU_SVA_SV
`define ACCU_SVA_SV

module accu_sva
(
  input logic         clk,
  input logic         rst_n,
  input logic [7:0]   data_in,
  input logic         valid_a,
  input logic         ready_b,

  input logic         ready_a,
  input logic         valid_b,
  input logic [7:0]   data_out,

  // internal DUT state
  input logic  [2:0]  count,
  input logic  [7:0]  adder_out_reg,
  input logic  [7:0]  mult_out_reg
);

  default clocking cb @(posedge clk); endclocking

  // Reset values come up correctly the cycle after rst_n deasserts low
  assert property (@(posedge clk) !rst_n |=> (valid_b == 1'b0 && data_out == 8'h00 && count == 3'd0));

  // All other properties disabled during reset
  default disable iff (!rst_n);

  // Handshake relationship
  assert property (ready_a == ~valid_b);

  // Count behavior
  assert property ((ready_b && valid_a && count != 3'd6) |=> count == $past(count)+3'd1);
  assert property ((ready_b && valid_a && count == 3'd6) |=> count == 3'd0);
  assert property (!(ready_b && valid_a) |=> $stable(count));
  assert property (count inside {[3'd0:3'd6]});

  // valid_b generation: only from a legal fire and as a 1-cycle pulse
  assert property (valid_b |-> $past(ready_b && valid_a && count == 3'd6));
  assert property ((ready_b && valid_a && count != 3'd6) |=> !valid_b);
  assert property (valid_b |=> !valid_b);

  // data_out update only when producing output, and with correct value
  assert property ((ready_b && valid_a && count == 3'd6)
                   |=> (valid_b && data_out == $past((adder_out_reg + mult_out_reg)/2)));
  assert property (!valid_b |-> $stable(data_out));

  // No X when outputting a valid result and operands are defined
  assert property ((ready_b && valid_a && count == 3'd6) |-> !$isunknown({adder_out_reg, mult_out_reg}));
  assert property (valid_b |-> !$isunknown({valid_b, data_out, ready_a}));

  // Coverage: observe a complete accumulation and output pulse
  cover property ((ready_b && valid_a)[*7] ##1 valid_b);
  cover property (valid_b ##1 !valid_b); // single-cycle pulse seen
  cover property ((ready_b && valid_a && count == 3'd6) ##1 (valid_b && ready_a == 1'b0));

endmodule

bind accu accu_sva u_accu_sva
(
  .clk           (clk),
  .rst_n         (rst_n),
  .data_in       (data_in),
  .valid_a       (valid_a),
  .ready_b       (ready_b),
  .ready_a       (ready_a),
  .valid_b       (valid_b),
  .data_out      (data_out),
  .count         (count),
  .adder_out_reg (adder_out_reg),
  .mult_out_reg  (mult_out_reg)
);

`endif