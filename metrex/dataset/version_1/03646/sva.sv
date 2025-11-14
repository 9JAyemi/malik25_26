// SVA for div_module
// Bind-friendly module that checks reset/load/shift behavior, muxing, outputs, count, and basic coverage.

module div_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  in1,
  input  logic [7:0]  in2,
  input  logic [15:0] out,
  input  logic [7:0]  remainder,

  // Internals
  input  logic [15:0] quotient_reg,
  input  logic [7:0]  remainder_reg,
  input  logic [7:0]  in2_reg,
  input  logic [7:0]  count_reg,
  input  logic [7:0]  in1_reg
);

  default clocking cb @(posedge clk); endclocking

  // Reset behavior: regs clear on the cycle after reset is sampled.
  assert property (reset |=> (quotient_reg == 16'd0
                           && remainder_reg == 8'd0
                           && in2_reg      == 8'd0
                           && count_reg    == 8'd0));

  // Outputs reflect internal regs
  assert property (out      == quotient_reg);
  assert property (remainder== remainder_reg);

  // Combinational mux for in1_reg
  assert property (in1_reg == ((count_reg == 8'd0) ? in1 : quotient_reg[7:0]));

  // Count increments and wraps
  assert property (disable iff (reset) count_reg == $past(count_reg)+8'd1);
  assert property (disable iff (reset) ($past(count_reg)==8'hFF) |-> (count_reg==8'h00));

  // Load phase when count==0 (uses inputs from that cycle)
  assert property ((count_reg == 8'd0) |=> (in2_reg               == $past(in2)
                                         && quotient_reg[15:8]    == $past(in1)
                                         && quotient_reg[7:0]     == 8'd0
                                         && remainder_reg         == 8'd0));

  // Shift/subtract phase when count!=0 (uses previous cycle values)
  assert property ((count_reg != 8'd0) |=> (quotient_reg          == {$past(quotient_reg[14:0]), $past(in1_reg[7])}
                                         && remainder_reg         == { $past(remainder_reg[6:0]),  $past(in1_reg[7]) } - $past(in2_reg)));

  // in2_reg must hold between load pulses
  assert property (disable iff (reset) ($past(count_reg)!=8'd0 && count_reg!=8'd0) |-> (in2_reg == $past(in2_reg)));

  // No Xs on key signals after reset deasserts
  assert property (disable iff (reset) !$isunknown({out, remainder, quotient_reg, remainder_reg, in2_reg, count_reg, in1_reg}));

  // Coverage
  cover property (reset ##1 !reset);                            // reset deassertion observed
  cover property ((count_reg==8'd0) ##1 (count_reg==8'd1));     // load followed by first shift
  cover property ((count_reg!=8'd0) ##1 (count_reg!=8'd0));     // consecutive shift cycles
  cover property (($past(count_reg)==8'hFF) ##1 (count_reg==8'h00)); // wrap-around
  cover property ((count_reg==8'd0) && (in1_reg==in1));         // in1_reg selects in1
  cover property ((count_reg!=8'd0) && (in1_reg==quotient_reg[7:0])); // in1_reg selects quotient_reg
  cover property ((count_reg!=8'd0) && (in1_reg[7]==1'b0));
  cover property ((count_reg!=8'd0) && (in1_reg[7]==1'b1));

endmodule

// Bind into the DUT
bind div_module div_module_sva sva_div_module (
  .clk(clk),
  .reset(reset),
  .in1(in1),
  .in2(in2),
  .out(out),
  .remainder(remainder),
  .quotient_reg(quotient_reg),
  .remainder_reg(remainder_reg),
  .in2_reg(in2_reg),
  .count_reg(count_reg),
  .in1_reg(in1_reg)
);