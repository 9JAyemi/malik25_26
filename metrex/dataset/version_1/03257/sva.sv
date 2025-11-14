// SVA for Multiplexer_AC__parameterized36
// Concise checks + useful coverage; bind-ready

`default_nettype none

module Multiplexer_AC__parameterized36_sva
(
  input logic [1:0] ctrl,
  input logic       D0,
  input logic       D1,
  input logic       D2,
  input logic       D3,
  input logic       S
);

  // Sample on any relevant edge (combinational checker)
  default clocking cb @(
      posedge ctrl[0] or negedge ctrl[0] or
      posedge ctrl[1] or negedge ctrl[1] or
      posedge D0      or negedge D0      or
      posedge D1      or negedge D1      or
      posedge D2      or negedge D2      or
      posedge D3      or negedge D3      or
      posedge S       or negedge S
  ); endclocking

  // Functional equivalence to mux equation
  assert property ( 1'b1 |-> S === ((ctrl==2'b00)?D0
                                  :(ctrl==2'b01)?D1
                                  :(ctrl==2'b10)?D2
                                  :(ctrl==2'b11)?D3
                                  :1'bx) )
    else $error("Mux equation mismatch");

  // Zero-latency selection per path
  assert property ((ctrl==2'b00) |-> ##0 (S === D0))
    else $error("S!=D0 when ctrl==00");
  assert property ((ctrl==2'b01) |-> ##0 (S === D1))
    else $error("S!=D1 when ctrl==01");
  assert property ((ctrl==2'b10) |-> ##0 (S === D2))
    else $error("S!=D2 when ctrl==10");
  assert property ((ctrl==2'b11) |-> ##0 (S === D3))
    else $error("S!=D3 when ctrl==11");

  // X behavior: unknown ctrl must drive unknown S
  assert property ($isunknown(ctrl) |-> $isunknown(S))
    else $error("ctrl X/Z must propagate to S");

  // When ctrl and selected data are known, S must be known
  assert property (
     (!$isunknown(ctrl) &&
      ((ctrl==2'b00 && !$isunknown(D0)) ||
       (ctrl==2'b01 && !$isunknown(D1)) ||
       (ctrl==2'b10 && !$isunknown(D2)) ||
       (ctrl==2'b11 && !$isunknown(D3)))))
     |-> !$isunknown(S))
    else $error("S is X despite valid select/data");

  // Coverage: hit all selects and observe data pass-through
  cover property (ctrl==2'b00 && S===D0);
  cover property (ctrl==2'b01 && S===D1);
  cover property (ctrl==2'b10 && S===D2);
  cover property (ctrl==2'b11 && S===D3);

  // Coverage: S activity
  cover property ($rose(S));
  cover property ($fell(S));

  // Coverage: transitions among selects
  cover property ((ctrl==2'b00) ##1 (ctrl==2'b01));
  cover property ((ctrl==2'b01) ##1 (ctrl==2'b10));
  cover property ((ctrl==2'b10) ##1 (ctrl==2'b11));
  cover property ((ctrl==2'b11) ##1 (ctrl==2'b00));

  // Coverage: X-propagation seen
  cover property ($isunknown(ctrl) && $isunknown(S));

endmodule

// Bind into DUT (map 1-bit vectors [0:0] to scalars)
bind Multiplexer_AC__parameterized36
  Multiplexer_AC__parameterized36_sva mux4_sva_bind (
    .ctrl(ctrl),
    .D0  (D0[0]),
    .D1  (D1[0]),
    .D2  (D2[0]),
    .D3  (D3[0]),
    .S   (S[0])
  );

`default_nettype wire