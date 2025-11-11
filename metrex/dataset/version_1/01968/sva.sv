// SVA for top_module
// Focused, concise checks + key coverage. Bind into DUT.

module top_module_sva;

  // Access DUT scope via bind; no ports needed.
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic X checks on key I/Os after first cycle
  assert property (past_valid |-> !$isunknown({count_out, swap_out, sum_out}));

  // Population-count pipeline as coded
  // shift_reg captures previous cycle's 'in' (effective behavior due to concat truncation)
  assert property (past_valid |-> shift_reg == $past(in));

  // Accumulator behavior
  assert property (past_valid |-> adder_out == $past(adder_out) + $past(in[254]));

  // count_out follows previous adder_out
  assert property (past_valid |-> count_out == $past(adder_out));

  // Byte-swap mapping (registered one-cycle)
  function automatic [31:0] swap32(input [31:0] x);
    swap32 = {x[7:0], x[15:8], x[23:16], x[31:24]};
  endfunction
  assert property (past_valid |-> swap_out == $past(swap32(in_swap)));

  // Sum operation (registered one-cycle)
  assert property (past_valid |-> sum_out == ($past(count_out) + $past(swap_out[31])));

  // Additional sanity: no X on internal state after first cycle
  assert property (past_valid |-> !$isunknown({adder_out, shift_reg}));

  // Coverage
  // - Observe both values of the driving bit into the accumulator
  cover property (past_valid && $changed(in[254]));
  // - Accumulator increments when previous in[254] == 1
  cover property (past_valid && (adder_out == $past(adder_out) + 1) && $past(in[254])==1);
  // - Accumulator holds when previous in[254] == 0
  cover property (past_valid && (adder_out == $past(adder_out)) && $past(in[254])==0);
  // - Wraparound on accumulator
  cover property (past_valid && (adder_out < $past(adder_out)));
  // - Byte-swap known pattern
  cover property (past_valid && (in_swap == 32'h01234567) ##1 (swap_out == 32'h67452301));
  // - sum_out reacts to MSB of swapped data
  cover property (past_valid && $past(swap_out[31]) && (sum_out == $past(count_out) + 1));
  cover property (past_valid && !$past(swap_out[31]) && (sum_out == $past(count_out)));

endmodule

bind top_module top_module_sva sva_inst;