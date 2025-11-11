// SVA for module acc
module acc_sva (
  input logic              clock,
  input logic              reset,
  input logic              clear,
  input logic              enable_in,
  input logic              enable_out,
  input logic signed [30:0] addend,
  input logic signed [33:0] sum
);

  default clocking cb @(posedge clock); endclocking

  // Helper: sign-extend 31->34
  function automatic signed [33:0] ext31to34(input signed [30:0] v);
    ext31to34 = v;
  endfunction

  // Basic sanity: controls must be 0/1
  assert property (!$isunknown({reset, clear, enable_in})) else $error("X/Z on control");

  // Reset branch: sum -> 0
  assert property (reset |=> sum == 34'sd0)
    else $error("sum after reset != 0");

  // Clear branch: sum -> addend (sign-extended)
  assert property ((!reset && clear) |=> sum == ext31to34($past(addend)))
    else $error("sum after clear != addend");

  // Accumulate branch: sum -> sum + addend (signed)
  assert property ((!reset && !clear && enable_in)
                   |=> sum == $past(sum) + ext31to34($past(addend)))
    else $error("sum accumulate mismatch");

  // Hold branch: sum holds when idle
  assert property ((!reset && !clear && !enable_in) |=> sum == $past(sum))
    else $error("sum not held");

  // enable_out is registered enable_in
  assert property (1'b1 |=> enable_out == $past(enable_in))
    else $error("enable_out != $past(enable_in)");

  // No X on outputs when driven by known inputs
  assert property (!$isunknown($past(enable_in)) |-> !$isunknown(enable_out))
    else $error("enable_out X with known past enable_in");
  assert property ((!reset && !$isunknown($past({clear,enable_in,addend}))) |-> !$isunknown(sum))
    else $error("sum X with known controls/addend");

  // Coverage: exercise all branches and priorities
  cover property (reset);
  cover property (!reset && clear);
  cover property (!reset && clear && enable_in);      // clear priority over enable_in
  cover property (reset && clear);                    // reset priority over clear
  cover property (!reset && !clear && enable_in);     // accumulate
  cover property ((!reset && !clear && enable_in)[*3]); // consecutive accumulates
  cover property (!reset && !clear && !enable_in);    // hold
  cover property ((!reset && clear) ##1 (!reset && !clear && enable_in)); // clear -> accumulate

endmodule

bind acc acc_sva acc_sva_i(.*);