// SVA for barrel_shifter
// Bind this file to the DUT
module barrel_shifter_sva (
  input clk,
  input reset,
  input [7:0] data_in,
  input [2:0] shift_amount,
  input shift_direction, // 0: right, 1: left
  input [7:0] data_out
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset drives zero immediately
  assert property (@(posedge reset) 1 |-> data_out == 8'h00)
    else $error("data_out not zero on posedge reset");

  // While reset is asserted, output stays zero
  assert property (cb reset |-> data_out == 8'h00)
    else $error("data_out not zero while reset=1");

  // Functional correctness (1-cycle latency). Guard out cycles following reset.
  // Left shift (zero-fill)
  assert property (cb disable iff (reset)
                   (!$past(reset) && $past(shift_direction))
                   |-> data_out == ($past(data_in) << $past(shift_amount)))
    else $error("Left shift result incorrect");

  // Right shift (zero-fill)
  assert property (cb disable iff (reset)
                   (!$past(reset) && !$past(shift_direction))
                   |-> data_out == ($past(data_in) >> $past(shift_amount)))
    else $error("Right shift result incorrect");

  // Zero shift is pass-through (both directions)
  assert property (cb disable iff (reset)
                   (!$past(reset) && ($past(shift_amount) == 3'd0))
                   |-> data_out == $past(data_in))
    else $error("Zero shift should be pass-through");

  // No X/Z on output when inputs are known (next cycle)
  assert property (cb disable iff (reset)
                   (!$past(reset) &&
                    !$isunknown($past({data_in, shift_amount, shift_direction})))
                   |-> !$isunknown(data_out))
    else $error("Unknown detected on data_out");

  // Input range check (defensive)
  assert property (cb shift_amount inside {[3'd0:3'd7]})
    else $error("shift_amount out of range");

  // Output stability when inputs are unchanged across cycles
  assert property (cb disable iff (reset)
                   (!$past(reset) &&
                    $past({data_in, shift_amount, shift_direction}) ==
                    {data_in, shift_amount, shift_direction})
                   |-> $stable(data_out))
    else $error("data_out changed despite identical inputs");

  // Functional coverage
  // - Hit both directions for all shift amounts
  genvar s;
  generate
    for (s = 0; s < 8; s++) begin : COV_S
      cover property (cb !reset && shift_direction && (shift_amount == s[2:0]));
      cover property (cb !reset && !shift_direction && (shift_amount == s[2:0]));
    end
  endgenerate

  // - Direction toggles
  cover property (cb !reset && $rose(shift_direction));
  cover property (cb !reset && $fell(shift_direction));

  // - Extremes
  cover property (cb !reset && shift_direction && shift_amount == 3'd0);
  cover property (cb !reset && !shift_direction && shift_amount == 3'd0);
  cover property (cb !reset && shift_direction && shift_amount == 3'd7);
  cover property (cb !reset && !shift_direction && shift_amount == 3'd7);

endmodule

bind barrel_shifter barrel_shifter_sva bsh_sva (
  .clk(clk),
  .reset(reset),
  .data_in(data_in),
  .shift_amount(shift_amount),
  .shift_direction(shift_direction),
  .data_out(data_out)
);