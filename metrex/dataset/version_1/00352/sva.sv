// SVA for top_module: concise, high-quality checks and coverage
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic        select,
  input logic [3:0]  counter,
  input logic        final_output
);

  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown(reset));

  // Known-value checks when out of reset
  assert property (!reset |-> !$isunknown({counter, final_output, select}));

  // Counter reset behavior (synchronous)
  assert property (reset |-> counter == 4'd0);

  // First cycle after reset deassert: counter starts from 1
  assert property ($past(reset) && !reset |-> counter == 4'd1);

  // Increment by 1 with 4-bit wrap when continuously out of reset
  assert property ($past(!reset) && !reset |-> counter == $past(counter) + 4'd1);

  // Final output mapping (note: final_output is 1-bit, uses LSB of counter)
  assert property (final_output == (select ? ~counter[0] : counter[0]));

  // Optional: during reset, counter==0 so final_output should equal select
  assert property (reset |-> final_output == select);

  // Coverage
  cover property (reset ##1 !reset);                                // reset toggle
  cover property (!reset && counter==4'hF ##1 !reset && counter==4'h0); // wrap 15->0
  cover property (!reset && !select && final_output==counter[0]);   // select=0 path
  cover property (!reset &&  select && final_output==~counter[0]);  // select=1 path
  cover property (!reset && $changed(select));                      // select toggles

endmodule

bind top_module top_module_sva sva_inst (.*);