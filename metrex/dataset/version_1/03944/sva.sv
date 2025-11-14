// synthesis translate_off
module mux_sva(input logic ctrl, input logic [0:0] D0, input logic [0:0] D1, input logic [0:0] S);

  // Functional equivalence (4-state accurate), zero-delay after any change
  property p_mux_func;
    @(ctrl or D0 or D1 or S)
      1'b1 |-> ##0 (S[0] === (ctrl ? D1[0] : D0[0]));
  endproperty
  assert property (p_mux_func);

  // X/Z select semantics coverage
  cover property (@(ctrl or D0 or D1)
    (ctrl !== 1'b0 && ctrl !== 1'b1 && D0[0] === D1[0]) ##0 (S[0] === D0[0]));
  cover property (@(ctrl or D0 or D1)
    (ctrl !== 1'b0 && ctrl !== 1'b1 && D0[0] !== D1[0]) ##0 (S[0] === 1'bx));

  // Data path coverage for each selection/value
  cover property (@(ctrl or D0) (ctrl === 1'b0 && D0[0] === 1'b0) ##0 (S[0] === 1'b0));
  cover property (@(ctrl or D0) (ctrl === 1'b0 && D0[0] === 1'b1) ##0 (S[0] === 1'b1));
  cover property (@(ctrl or D1) (ctrl === 1'b1 && D1[0] === 1'b0) ##0 (S[0] === 1'b0));
  cover property (@(ctrl or D1) (ctrl === 1'b1 && D1[0] === 1'b1) ##0 (S[0] === 1'b1));

  // Control toggle coverage with correct selection
  cover property (@(posedge ctrl) ##0 (S[0] === D1[0]));
  cover property (@(negedge ctrl) ##0 (S[0] === D0[0]));

  // Selected-input tracking coverage (zero-latency)
  cover property (@(D0) (ctrl === 1'b0) ##0 (S[0] === D0[0]));
  cover property (@(D1) (ctrl === 1'b1) ##0 (S[0] === D1[0]));

endmodule

// Bind into the DUT
bind mux mux_sva mux_sva_i(.ctrl(ctrl), .D0(D0), .D1(D1), .S(S));
// synthesis translate_on