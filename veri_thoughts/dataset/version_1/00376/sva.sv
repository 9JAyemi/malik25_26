// SVA for top_module and sub-blocks (concise, quality-focused)
module top_module_sva (
  input clk,
  input reset,
  input [7:0] in1,
  input [7:0] in2,
  input select,
  input [7:0] out,
  input [7:0] adder1_out,
  input [7:0] adder2_out,
  input [7:0] and_out
);
  default clocking cb @(posedge clk); endclocking

  // Adders compute registered sum of previous-cycle inputs (mod 256)
  assert property ( !$past(reset) |-> (adder1_out == $past((in1+in2)[7:0])) );
  assert property ( !$past(reset) |-> (adder2_out == $past((in1+in2)[7:0])) );

  // Synchronous reset drives registered outputs to 0 on next cycle
  assert property ( reset |=> (adder1_out == 8'h00) );
  assert property ( reset |=> (adder2_out == 8'h00) );

  // The two adders must always agree when known
  assert property ( (!$isunknown({adder1_out,adder2_out})) |-> (adder1_out == adder2_out) );

  // Control logic: AND is symmetric and independent of select value
  assert property ( and_out == (adder1_out & adder2_out) );

  // Top-level connectivity and functional end-to-end check
  assert property ( out == and_out );
  assert property ( !$past(reset) |-> (out == $past((in1+in2)[7:0])) );
  assert property ( reset |=> (out == 8'h00) );

  // Minimal functional coverage
  cover property ( $rose(reset) );
  cover property ( $fell(reset) );
  cover property ( $rose(select) );
  cover property ( $fell(select) );
  // Overflow/wrap example: FF + 01 -> 00 (mod 256) on next cycle
  cover property ( !$past(reset) && $past(in1)==8'hFF && $past(in2)==8'h01 ##1 (out==8'h00) );
endmodule

// Bind into DUT (internal wires are connected via hierarchical names in the bind scope)
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .reset(reset),
  .in1(in1),
  .in2(in2),
  .select(select),
  .out(out),
  .adder1_out(adder1_out),
  .adder2_out(adder2_out),
  .and_out(and_out)
);