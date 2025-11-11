// SVA for Multiplexer
// Bind this checker to the DUT for concise, high-quality assertions and coverage.

module mux_sva #(parameter WIDTH = 1)
(
  input  logic              ctrl,
  input  logic [WIDTH-1:0]  D0,
  input  logic [WIDTH-1:0]  D1,
  input  logic [WIDTH-1:0]  S
);

  // Functional correctness (use ##0 to avoid race with continuous assign)
  assert property (@(ctrl or D0 or D1) (ctrl===1'b0) |-> ##0 (S===D0))
    else $error("MUX: S must equal D0 when ctrl==0");

  assert property (@(ctrl or D0 or D1) (ctrl===1'b1) |-> ##0 (S===D1))
    else $error("MUX: S must equal D1 when ctrl==1");

  // Unknown handling: if ctrl is X/Z and D0==D1, S must equal that common value
  assert property (@(ctrl or D0 or D1) ($isunknown(ctrl) && (D0===D1)) |-> ##0 (S===D0))
    else $error("MUX: With unknown ctrl and equal inputs, S must equal that value");

  // No X/Z on S when selected input and ctrl are known
  assert property (@(ctrl or D0 or D1) (ctrl===1'b0 && !$isunknown(D0)) |-> ##0 !$isunknown(S))
    else $error("MUX: S became unknown while selecting known D0");

  assert property (@(ctrl or D0 or D1) (ctrl===1'b1 && !$isunknown(D1)) |-> ##0 !$isunknown(S))
    else $error("MUX: S became unknown while selecting known D1");

  // Minimal but meaningful coverage
  cover property (@(ctrl) ctrl===1'b0);
  cover property (@(ctrl) ctrl===1'b1);

  // Per-bit propagation coverage (both 0 and 1 propagate from each leg)
  genvar i;
  generate
    for (i=0; i<WIDTH; i++) begin : gen_cov_bits
      cover property (@(D0[i] or ctrl) (ctrl===1'b0 && D0[i]===1'b0) ##0 (S[i]===1'b0));
      cover property (@(D0[i] or ctrl) (ctrl===1'b0 && D0[i]===1'b1) ##0 (S[i]===1'b1));
      cover property (@(D1[i] or ctrl) (ctrl===1'b1 && D1[i]===1'b0) ##0 (S[i]===1'b0));
      cover property (@(D1[i] or ctrl) (ctrl===1'b1 && D1[i]===1'b1) ##0 (S[i]===1'b1));
    end
  endgenerate

  // Corner-case coverage: unknown ctrl with differing inputs observed
  cover property (@(ctrl or D0 or D1) ($isunknown(ctrl) && (D0!==D1)));

endmodule

// Bind to the DUT
bind Multiplexer mux_sva #(.WIDTH(WIDTH)) mux_sva_i (.ctrl(ctrl), .D0(D0), .D1(D1), .S(S));