// SVA for top_module. Bind this to the DUT.
// Focus: reset behavior, counters/increments with wrap, split/combine correctness, X-checks, and concise coverage.

module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  counter,
  input logic [15:0] input_num,
  input logic [7:0]  out_hi,
  input logic [7:0]  out_lo,
  input logic [15:0] final_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset clears
  assert property (reset |-> (counter==4'd0 && input_num==16'd0));

  // First cycle after reset deassert -> increment from 0 to 1
  assert property ((!reset && $past(reset)) |-> (counter==4'd1 && input_num==16'd1));

  // Increment behavior with wrap when not in/reset
  assert property ((!reset && $past(!reset)) |->
                   (( $past(counter)!=4'hF)   ? (counter==$past(counter)+1) : (counter==4'h0)) &&
                   (( $past(input_num)!=16'hFFFF) ? (input_num==$past(input_num)+1) : (input_num==16'h0000)));

  // Splitter correctness
  assert property (out_hi == input_num[15:8]);
  assert property (out_lo == input_num[7:0]);

  // Combiner correctness and end-to-end equivalence
  assert property (final_out == {out_hi, out_lo});
  assert property (final_out == input_num);

  // No X/Z on key signals after reset releases
  assert property (disable iff (reset) !$isunknown({counter,input_num,out_hi,out_lo,final_out}));

  // Coverage
  cover property (reset ##1 !reset); // saw a reset pulse
  cover property ($past(!reset) && !reset && $past(counter)==4'hF && counter==4'h0); // 4-bit wrap
  cover property ($past(!reset) && !reset && $past(input_num[7:0])==8'hFF &&
                  input_num[7:0]==8'h00 && input_num[15:8]==$past(input_num[15:8])+1); // byte carry
  cover property (!reset && final_out==input_num); // end-to-end match observed
endmodule

bind top_module top_module_sva i_top_module_sva (
  .clk(clk),
  .reset(reset),
  .counter(counter),
  .input_num(input_num),
  .out_hi(out_hi),
  .out_lo(out_lo),
  .final_out(final_out)
);