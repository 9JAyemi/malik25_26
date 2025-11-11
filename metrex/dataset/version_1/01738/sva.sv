// SVA for iq_comp. Bind this to the DUT.
// Focused, high-quality checks and key coverage.

module iq_comp_sva (
  input logic                       clk,
  input logic                       RESETn,
  input logic                       freeze_iqcomp,
  input logic        [1:0]          op_mode,
  input logic signed [3:0]          Ix,
  input logic signed [3:0]          Qx,
  input logic signed [12:0]         Wr_in,
  input logic signed [12:0]         Wj_in,
  input logic signed [3:0]          Iy,
  input logic signed [3:0]          Qy,
  input logic                       settled,
  input logic signed [12:0]         Wr,
  input logic signed [12:0]         Wj
);

  default clocking cb @(posedge clk); endclocking

  // Helpful lets for truncation overflow coverage
  let ty = ($past(Ix) - $past(Wr_in) * $past(Qx)); // 17-bit signed
  let tq = ($past(Qx) + $past(Wj_in) * $past(Ix)); // 17-bit signed

  // Basic X-propagation hygiene
  a_no_x_inputs:  assert property (disable iff (!RESETn) !$isunknown({freeze_iqcomp, Ix, Qx, Wr_in, Wj_in, op_mode}));
  a_no_x_outputs: assert property (disable iff (!RESETn) !$isunknown({Iy, Qy, Wr, Wj, settled}));

  // Synchronous reset clears on next clock
  a_reset_clears: assert property (!RESETn |=> Iy==0 && Qy==0 && Wr==0 && Wj==0 && settled==0);

  // Freeze: hold all data outputs and force settled low on next clock
  a_freeze_holds: assert property (disable iff (!RESETn)
                                   freeze_iqcomp |=> Iy==$past(Iy) && Qy==$past(Qy) &&
                                                     Wr==$past(Wr) && Wj==$past(Wj) && !settled);

  // Unfrozen: compute/tracking and settled high on next clock
  a_update_unfrozen: assert property (disable iff (!RESETn)
                                      !freeze_iqcomp |=> settled &&
                                      Iy == $signed( ($past(Ix) - $past(Wr_in)*$past(Qx))[3:0] ) &&
                                      Qy == $signed( ($past(Qx) + $past(Wj_in)*$past(Ix))[3:0] ) &&
                                      Wr == $past(Wr_in) && Wj == $past(Wj_in));

  // Settled mirrors freeze each cycle (redundant with above but explicit)
  a_settled_low_when_frozen:  assert property (disable iff (!RESETn)  freeze_iqcomp  |=> !settled);
  a_settled_high_when_active: assert property (disable iff (!RESETn) !freeze_iqcomp |=>  settled);

  // Core functional coverage
  c_reset_to_active:  cover property (!RESETn ##1 RESETn ##1 !freeze_iqcomp ##1 settled);
  c_freeze_hold:      cover property (disable iff (!RESETn) freeze_iqcomp ##1 $stable({Iy,Qy,Wr,Wj}) && !settled);
  c_toggle_freeze:    cover property (disable iff (!RESETn) !freeze_iqcomp ##1 freeze_iqcomp ##1 !freeze_iqcomp);

  // Arithmetic truncation coverage (overflow into 4-bit signed)
  c_trunc_overflow:   cover property (disable iff (!RESETn)
                                      !freeze_iqcomp ##1
                                      ( (ty[16:4] != {13{ty[3]}}) || (tq[16:4] != {13{tq[3]}}) ));
  c_no_overflow:      cover property (disable iff (!RESETn)
                                      !freeze_iqcomp ##1
                                      ( (ty[16:4] == {13{ty[3]}}) && (tq[16:4] == {13{tq[3]}}) ));

endmodule

bind iq_comp iq_comp_sva i_iq_comp_sva (.*);