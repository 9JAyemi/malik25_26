// SystemVerilog Assertions for top_module and its submodules
// Focus: correctness, reset behavior, equivalence, and concise coverage

// Assertions for the registered adder
module adder_sva (
  input logic        clk,
  input logic        reset,
  input logic [7:0]  in1,
  input logic [7:0]  in2,
  input logic [7:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // Reset drives output to 0 on the very next sampled cycle
  a_reset_clears: assert property ( $past(reset) |-> (out == 8'h00) );

  // Functional correctness when not in or just exiting reset
  a_sum_correct: assert property (
    (!reset && !$past(reset)) |-> (out == ($past(in1) + $past(in2)))
  );

  // If inputs hold and not in reset, the registered sum holds
  a_hold_when_inputs_hold: assert property (
    (!reset && !$past(reset) && $stable({in1,in2})) |-> (out == $past(out))
  );

  // Cleanliness: no X/Z on output when out is functionally used
  a_no_x_out: assert property ( !reset |-> !$isunknown(out) );

  // Coverage: reset deassertion observed
  c_reset_deassert: cover property ( $past(reset) && !reset );

  // Coverage: observe an 8-bit addition overflow (carry out of bit 7)
  c_overflow: cover property (
    !reset && !$past(reset) &&
    (({1'b0,$past(in1)} + {1'b0,$past(in2)})[8] == 1'b1)
  );
endmodule

// Top-level assertions tying everything together
module top_sva (
  input  logic       clk,
  input  logic       reset,
  input  logic       select,
  input  logic [7:0] out,
  input  logic [7:0] adder1_out,
  input  logic [7:0] adder2_out,
  input  logic [7:0] and_out
);
  default clocking cb @(posedge clk); endclocking

  // Connectivity: top out equals internal AND output
  a_out_connect: assert property ( out == and_out );

  // Control-logic correctness (commutative AND, independent of select)
  a_and_correct: assert property ( and_out == (adder1_out & adder2_out) );

  // Both adders should always match (identical inputs and logic)
  a_adders_match: assert property ( !reset |-> (adder1_out == adder2_out) );

  // No X/Z on key observable signals during functional operation
  a_no_x_top: assert property (
    !reset |-> (!$isunknown(out) && !$isunknown(adder1_out) && !$isunknown(adder2_out))
  );

  // Coverage: both select values seen during operation
  c_sel0: cover property ( !reset && (select == 1'b0) );
  c_sel1: cover property ( !reset && (select == 1'b1) );

  // Coverage: AND result becomes non-zero during operation
  c_and_nonzero: cover property ( !reset && (and_out != 8'h00) );
endmodule

// Bind SVA to instances
bind adder       adder_sva u_adder_sva ( .clk(clk), .reset(reset), .in1(in1), .in2(in2), .out(out) );
bind top_module  top_sva   u_top_sva   ( .clk(clk), .reset(reset), .select(select),
                                         .out(out),
                                         .adder1_out(adder1_out),
                                         .adder2_out(adder2_out),
                                         .and_out(and_out) );