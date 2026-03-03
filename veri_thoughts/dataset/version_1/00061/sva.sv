// SVA for counter: concise, high-quality checks + targeted coverage
module counter_sva(input logic clk, rst, en, input logic [1:0] count);

  default clocking cb @ (posedge clk); endclocking

  // Guard $past on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Functional correctness
  // 1) Synchronous reset clears to 0 (rst has priority over en)
  assert property (rst |=> count == 2'd0);

  // 2) Increment by 1 when enabled (mod-4)
  assert property (disable iff (!past_valid or rst)
                   en |=> count == $past(count) + 2'd1);

  // 3) Hold when not enabled
  assert property (disable iff (!past_valid or rst)
                   !en |=> count == $past(count));

  // 4) Count only changes (outside reset) when en is asserted
  assert property (disable iff (!past_valid or rst)
                   (count != $past(count)) |-> en);

  // Targeted coverage
  // A) Exercise full rollover with en held high for 4 cycles
  cover property (disable iff (!past_valid or rst)
                  count == 2'd0 ##1 en ##1 count == 2'd1 ##1
                  en ##1 count == 2'd2 ##1 en ##1 count == 2'd3 ##1
                  en ##1 count == 2'd0);

  // B) Exercise wrap from 3 -> 0
  cover property (disable iff (!past_valid or rst)
                  count == 2'd3 && en |=> count == 2'd0);

  // C) Exercise hold when disabled
  cover property (disable iff (!past_valid or rst)
                  !en |=> $stable(count));

  // D) Exercise reset from non-zero to zero
  cover property (past_valid && !rst && count != 2'd0 ##1 rst ##1 count == 2'd0);

endmodule

// Bind into DUT
bind counter counter_sva i_counter_sva(.clk(clk), .rst(rst), .en(en), .count(count));