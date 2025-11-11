// SVA for sky130_fd_sc_ms__o31a: X = (A1 | A2 | A3) & B1
// Bind into every instance; assertions are concise and 4-state aware.
module sky130_fd_sc_ms__o31a_sva (
  input logic A1, A2, A3, B1,
  input logic X
);

  // Combinational equivalence (deferred to end of timestep for delta-cycles)
  always_comb begin
    assert final (X === ((A1 | A2 | A3) & B1))
      else $error("o31a comb mismatch: X=%b exp=%b A=%b%b%b B1=%b",
                  X, ((A1|A2|A3)&B1), A1, A2, A3, B1);
  end

  // Strong gating: B1 low forces X low (even with unknown A's)
  property p_b1_low_forces_0;
    @(A1 or A2 or A3 or B1 or X) (B1 === 1'b0) |-> (X === 1'b0);
  endproperty
  assert property (p_b1_low_forces_0);

  // When B1 high:
  // - any A high forces X high
  property p_b1_high_anyA_high_X_high;
    @(A1 or A2 or A3 or B1 or X)
      (B1 === 1'b1 && (A1 === 1'b1 || A2 === 1'b1 || A3 === 1'b1)) |-> (X === 1'b1);
  endproperty
  assert property (p_b1_high_anyA_high_X_high);

  // - all A low forces X low
  property p_b1_high_allA_low_X_low;
    @(A1 or A2 or A3 or B1 or X)
      (B1 === 1'b1 && A1 === 1'b0 && A2 === 1'b0 && A3 === 1'b0) |-> (X === 1'b0);
  endproperty
  assert property (p_b1_high_allA_low_X_low);

  // No X/Z on X when all inputs are known 0/1
  function automatic bit is_known(input logic v); return (v !== 1'bx && v !== 1'bz); endfunction
  property p_no_x_when_inputs_known;
    @(A1 or A2 or A3 or B1 or X)
      (is_known(A1) && is_known(A2) && is_known(A3) && is_known(B1)) |-> is_known(X);
  endproperty
  assert property (p_no_x_when_inputs_known);

  // X must not change due to A-changes while B1 is 0
  property p_stable_when_disabled;
    @(A1 or A2 or A3) (B1 === 1'b0) |-> $stable(X);
  endproperty
  assert property (p_stable_when_disabled);

  // Functional coverage of key corners
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===1 && A2===0 && A3===0 && X===1));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===0 && A2===1 && A3===0 && X===1));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===0 && A2===0 && A3===1 && X===1));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===1 && A1===0 && A2===0 && A3===0 && X===0));
  cover property (@(A1 or A2 or A3 or B1 or X) (B1===0 && X===0));
  // Output toggles
  cover property (@(posedge X) 1);
  cover property (@(negedge X) 1);

endmodule

bind sky130_fd_sc_ms__o31a sky130_fd_sc_ms__o31a_sva o31a_sva_bind (.*);