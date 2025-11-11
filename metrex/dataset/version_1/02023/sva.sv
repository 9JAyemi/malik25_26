// SVA for Multiplexer_AC__parameterized61
// Concise, high-quality checks and coverage for 1-bit 2:1 mux (4-state semantics)

module Multiplexer_AC__parameterized61_sva (
  input  logic        ctrl,
  input  logic [0:0]  D0,
  input  logic [0:0]  D1,
  input  logic [0:0]  S
);

  // Core functional check (allow a delta to settle combinational assign)
  assert property (@(ctrl or D0 or D1 or S) ##0 (S === (ctrl ? D1 : D0)))
    else $error("MUX functional mismatch: S != (ctrl ? D1 : D0)");

  // When selection is fully known, output must be known (no unintended X/Z propagation)
  assert property (@(ctrl or D0 or D1)
                   (! $isunknown(ctrl) && ! $isunknown(ctrl ? D1 : D0))
                   |-> ##0 ! $isunknown(S))
    else $error("MUX produced X/Z with known select and selected data");

  // Coverage: exercise both selects, edges, and X-ambiguous behavior
  cover property (@(negedge ctrl) ##0 (S === D0));              // select D0
  cover property (@(posedge ctrl) ##0 (S === D1));              // select D1
  cover property (@(ctrl or D0 or D1) ##0 ($isunknown(ctrl) &&
                                           (D0 !== D1) &&
                                           $isunknown(S)));     // X-ambiguous case
  cover property (@(posedge S[0]));                             // S rises
  cover property (@(negedge S[0]));                             // S falls

endmodule

bind Multiplexer_AC__parameterized61 Multiplexer_AC__parameterized61_sva u_sva (
  .ctrl(ctrl), .D0(D0), .D1(D1), .S(S)
);