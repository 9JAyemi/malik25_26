// SVA for Shift_Register
// Bind into DUT to access internals (shift_reg, params)
module Shift_Register_sva;

  // Elaboration-time parameter sanity
  initial begin
    assert (w >= m)
      else $error("Shift_Register SVA: require w >= m, got w=%0d m=%0d", w, m);
    assert (n == m)
      else $error("Shift_Register SVA: require n == m so {shift_reg[w-1:m], in} width == w (n=%0d m=%0d)", n, m);
  end

  // Use ctrl as clock
  default clocking cb @ (posedge ctrl); endclocking

  // Clock must be known at sampling edge
  assert property ( !$isunknown(ctrl) )
    else $error("Shift_Register SVA: ctrl is X at posedge");

  // After each posedge (post-NBA), low m bits load 'in'
  assert property ( ##0 (shift_reg[m-1:0] == in) )
    else $error("Shift_Register SVA: LSBs not loaded with 'in'");

  // out mirrors low m bits (post-NBA)
  assert property ( ##0 (out == shift_reg[m-1:0]) )
    else $error("Shift_Register SVA: out != shift_reg[m-1:0]");

  // Full next-state functional check
  assert property ( $past(1'b1) |-> ##0 (shift_reg == { $past(shift_reg)[w-1:m], in }) )
    else $error("Shift_Register SVA: shift_reg' != {shift_reg[w-1:m], in}");

  // High bits remain unchanged across updates (as implemented)
  assert property ( $past(1'b1) |-> ##0 (shift_reg[w-1:m] == $past(shift_reg)[w-1:m]) )
    else $error("Shift_Register SVA: upper bits changed unexpectedly");

  // If 'in' known at edge, 'out' becomes known after update
  assert property ( (!$isunknown(in)) |-> ##0 (!$isunknown(out)) )
    else $error("Shift_Register SVA: out is X despite known in");

  // out changes only in timesteps that include a ctrl posedge (no glitches between edges)
  property p_out_changes_only_on_clk;
    @(posedge ctrl or out) $changed(out) |-> $rose(ctrl);
  endproperty
  assert property (p_out_changes_only_on_clk)
    else $error("Shift_Register SVA: out changed without ctrl posedge");

  // Coverage
  cover property ( $rose(ctrl) );
  cover property ( @(posedge ctrl) ##0 (out == in) );
  cover property ( @(posedge ctrl) $past(1'b1) && (in != $past(in)) ); // observe two different inputs on consecutive edges

endmodule

bind Shift_Register Shift_Register_sva;