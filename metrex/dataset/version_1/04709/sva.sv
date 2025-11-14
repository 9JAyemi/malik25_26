// SVA for shift_register
// Binds into the DUT and checks next-state function and output registration concisely.

module shift_register_sva;
  // Implicitly bound into shift_register scope; directly uses clk, reset, load, data_in, shift_reg, data_out
  default clocking cb @(posedge clk); endclocking

  // Core next-state check for shift_reg (handles reset priority, load zero-extend, rotate-left-by-1)
  // Checks state at time t equals function of inputs/state at t-1
  assert property ($past(1'b1) |-> 
                   shift_reg == ( $past(reset) ? 8'h00 :
                                  $past(load)  ? {7'b0, $past(data_in)} :
                                                 { $past(shift_reg[6:0]), $past(shift_reg[7]) } ))
    else $error("shift_reg next-state mismatch");

  // data_out is registered MSB of shift_reg (zero-extended into [7:0])
  assert property ($past(1'b1) |-> data_out == {7'b0, $past(shift_reg[7])})
    else $error("data_out does not match registered MSB of shift_reg");

  // Sanity: upper bits of data_out are always 0 due to 1-bit assignment
  assert property (data_out[7:1] == '0)
    else $error("data_out[7:1] must be 0");

  // Reset has priority over load
  assert property ($past(reset) && $past(load) |-> shift_reg == 8'h00)
    else $error("Reset did not take priority over load");

  // Optional: flag unknowns on inputs at sampling (helps catch TB/DUT Xs)
  assert property (!$isunknown({reset, load, data_in}))
    else $error("Input contains X/Z at clock edge");

  // Coverage: reset seen
  cover property (reset);

  // Coverage: load 0 and 1 observed
  cover property (load && !data_in);
  cover property (load &&  data_in);

  // Coverage: After loading a '1', eight pure rotates lead to a data_out pulse
  sequence s_8rot; (!reset && !load)[*8]; endsequence
  cover property ( (load && data_in) ##1 s_8rot ##1 data_out[0] );
endmodule

bind shift_register shift_register_sva sva_inst();