// SVA for shift_register
// Binds to the DUT; focuses on reset behavior, functional relation,
// X/Z checks, and concise coverage.

module shift_register_sva (
  input        clk,
  input        reset,
  input  [7:0] data_in,
  input  [7:0] data_out
);

  default clocking cb @(posedge clk); endclocking

  // Reset must clear output on the next cycle
  property p_reset_clears_next;
    reset |=> (data_out == 8'h00);
  endproperty
  assert property (p_reset_clears_next)
    else $error("shift_register: data_out not cleared after reset");

  // While checking functional behavior, avoid X/Z on inputs/outputs
  // After a clean cycle (no reset now or previous), last data_in must be known
  assert property ( (!reset && !$past(reset)) |-> !$isunknown($past(data_in)) )
    else $error("shift_register: data_in unknown when sampled");
  // Never drive X/Z on data_out when not in reset
  assert property ( disable iff (reset) !$isunknown(data_out) )
    else $error("shift_register: data_out has X/Z outside reset");

  // Functional behavior per given RTL:
  // When not in reset for two consecutive cycles, data_out is the previous data_in (1-cycle pipeline)
  property p_one_cycle_load;
    (!reset && !$past(reset)) |-> (data_out == $past(data_in));
  endproperty
  assert property (p_one_cycle_load)
    else $error("shift_register: data_out != previous data_in");

  // Simple coverages
  cover property (reset ##1 !reset);                                // reset deassert sequence
  cover property (!reset && !$past(reset) ##1 data_out == $past(data_in)); // exercised load
  cover property (!reset && !$past(reset) ##1 data_out != $past(data_out)); // output change

endmodule

bind shift_register shift_register_sva sva_i (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .data_out(data_out)
);