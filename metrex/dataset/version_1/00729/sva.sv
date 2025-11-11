// SVA for module pulse
// Bind example (instantiate once per DUT instance):
// bind pulse pulse_sva #(.dly(dly), .len(len)) u_pulse_sva (.* , .cnt(cnt));

module pulse_sva #(parameter int dly=3, parameter int len=2)
(
  input logic clk,
  input logic rstn,
  input logic pulse,
  input logic [($clog2(dly+len)+1)-1:0] cnt
);

  // Static parameter sanity
  initial begin
    assert (len > 0) else $error("len must be > 0");
    assert (dly >= 0) else $error("dly must be >= 0");
  end

  default clocking cb @(posedge clk); endclocking

  // Reset values hold while in reset
  assert property (@cb !rstn |-> (cnt==0 && pulse==0));

  // No X/Z when out of reset
  assert property (@cb rstn |-> !$isunknown({cnt,pulse}));

  // Counter bounds and saturation
  assert property (@cb cnt <= dly+len);
  assert property (@cb disable iff (!rstn)
                   ($past(cnt) != dly+len) |-> (cnt == $past(cnt)+1));
  assert property (@cb disable iff (!rstn)
                   ($past(cnt) == dly+len) |-> (cnt == dly+len));

  // Pulse value vs counter
  assert property (@cb (cnt < dly) |-> !pulse);
  assert property (@cb (cnt inside {[dly : dly+len-1]}) |-> pulse);
  assert property (@cb (cnt == dly+len) |-> !pulse);

  // Pulse edges occur only at the specified counts
  assert property (@cb disable iff (!rstn) $rose(pulse) |-> (cnt == dly));
  assert property (@cb disable iff (!rstn) $fell(pulse) |-> (cnt == dly+len));

  // Pulse length is exactly 'len' cycles
  assert property (@cb disable iff (!rstn) $rose(pulse) |-> ##len $fell(pulse));

  // Post-terminal stability
  assert property (@cb (cnt == dly+len) |-> (!pulse && $stable(pulse) && $stable(cnt)));

  // Functional coverage
  cover property (@cb $rose(rstn) ##1 !pulse[*dly] ##1 pulse[*len] ##1 !pulse);
  cover property (@cb $rose(pulse));
  cover property (@cb $fell(pulse));
  cover property (@cb cnt == dly+len);

endmodule