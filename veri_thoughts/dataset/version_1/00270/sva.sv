// SVA checker for logic_circuit
module logic_circuit_sva (
  input logic A1, A2, B1, B2,
  input logic or0_out, or1_out, and0_out_X,
  input logic X
);
  // Knownness helpers
  wire in_k      = !$isunknown({A1,A2,B1,B2});
  wire or0_in_k  = !$isunknown({A1,A2});
  wire or1_in_k  = !$isunknown({B1,B2});
  wire and_in_k  = !$isunknown({or0_out,or1_out});
  wire buf_in_k  = !$isunknown(and0_out_X);

  // Functional correctness (gate-by-gate and end-to-end), only when inputs are known
  assert property (or0_in_k |-> or0_out    == (A1 | A2));
  assert property (or1_in_k |-> or1_out    == (B1 | B2));
  assert property (and_in_k |-> and0_out_X == (or0_out & or1_out));
  assert property (buf_in_k |-> X          == and0_out_X);
  assert property (in_k     |-> X          == ((A1 | A2) & (B1 | B2)));

  // No X/Z propagation when primary inputs are known
  assert property (in_k |-> !$isunknown({or0_out,or1_out,and0_out_X,X}));

  // Strong implications at the AND stage (when known)
  assert property (and_in_k && ((or0_out==1'b0) || (or1_out==1'b0)) |-> X==1'b0);
  assert property (and_in_k &&  (or0_out==1'b1) && (or1_out==1'b1)  |-> X==1'b1);

  // Coverage: all 16 input combinations
  genvar i;
  for (i=0; i<16; i++) begin : g_cov_in
    localparam logic [3:0] V = i[3:0];
    cover property ({A1,A2,B1,B2} == V);
  end

  // Coverage: observe both X=0 and X=1 (and transitions)
  cover property (X==1'b0);
  cover property (X==1'b1);
  cover property ($rose(X));
  cover property ($fell(X));
endmodule

// Bind into DUT (accesses internal nets)
bind logic_circuit logic_circuit_sva u_logic_circuit_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2),
  .or0_out(or0_out), .or1_out(or1_out), .and0_out_X(and0_out_X),
  .X(X)
);