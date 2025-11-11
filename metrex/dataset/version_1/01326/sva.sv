// SVA for and_gate_ctrl
// Note: DUT out is 1-bit but is driven by a 4-bit expression; assertions below
// check the effective behavior (only bit[0] of a,b,c,d contributes to out).

module and_gate_ctrl_sva_checker #(
  parameter bit ENABLE_PWR_CHECKS = 1
)(
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic [3:0] c,
  input  logic [3:0] d,
  input  logic       ctrl,
  input  logic       vdd,
  input  logic       gnd,
  input  logic       out
);

  default clocking cb @(posedge $global_clock); endclocking

  // Expected behavior (effective LSB-only due to DUT width)
  logic exp_and_lsb, exp_out;
  assign exp_and_lsb = a[0] & b[0] & c[0] & d[0];
  assign exp_out     = ctrl ? ~exp_and_lsb : exp_and_lsb;

  // X/Z clean on used signals
  assert property (!$isunknown({a,b,c,d,ctrl})))
    else $error("and_gate_ctrl: X/Z on inputs");
  assert property (!$isunknown(out)))
    else $error("and_gate_ctrl: X/Z on out");

  // Functional equivalence
  assert property (1'b1 |-> (out === exp_out))
    else $error("and_gate_ctrl: functional mismatch");

  // Out stable when all drivers are stable
  assert property ($stable({a,b,c,d,ctrl}) |-> $stable(out))
    else $error("and_gate_ctrl: out changed while inputs stable");

  // Toggling ctrl complements out when data stable
  assert property ($changed(ctrl) && $stable({a,b,c,d}) |-> out == ~$past(out))
    else $error("and_gate_ctrl: ctrl toggle did not invert out");

  // Optional power pin checks
  if (ENABLE_PWR_CHECKS) begin
    assert property (!($isunknown(vdd) || $isunknown(gnd)))
      else $error("and_gate_ctrl: X/Z on power pins");
    assert property (vdd === 1'b1)
      else $error("and_gate_ctrl: vdd != 1");
    assert property (gnd === 1'b0)
      else $error("and_gate_ctrl: gnd != 0");
  end

  // Coverage
  cover property (ctrl == 1'b0 && out == 1'b0);
  cover property (ctrl == 1'b0 && out == 1'b1);
  cover property (ctrl == 1'b1 && out == 1'b0);
  cover property (ctrl == 1'b1 && out == 1'b1);
  cover property ($changed(ctrl) && $stable({a,b,c,d}) && out == ~$past(out));
  cover property (exp_and_lsb == 1'b0);
  cover property (exp_and_lsb == 1'b1);

endmodule

// Bind into the DUT
bind and_gate_ctrl and_gate_ctrl_sva_checker i_and_gate_ctrl_sva_checker(
  .a(a), .b(b), .c(c), .d(d),
  .ctrl(ctrl), .vdd(vdd), .gnd(gnd),
  .out(out)
);