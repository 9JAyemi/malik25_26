// SVA checkers for BitsliceALU and Circuit74181b
// Bind these to the DUTs to verify combinational correctness and provide concise coverage.

module BitsliceALU_sva;
  // clockless concurrent assertions driven by any comb change
  event comb_ev; always @* -> comb_ev;
  default clocking @(comb_ev); endclocking

  function automatic [3:0] nib_g(input [3:0] a,b);
    logic [3:0] P,G;
    begin
      P = a & b;
      G = a | b;
      nib_g[0] = P[0];
      nib_g[1] = P[1] | (P[0] & G[1]);
      nib_g[2] = P[2] | (P[1] & G[2]) | (P[0] & G[1] & G[2]);
      nib_g[3] = P[3] | (P[2] & G[3]) | (P[1] & G[2] & G[3]) | (P[0] & G[1] & G[2] & G[3]);
    end
  endfunction

  // Q functional correctness (independent of Op)
  assert property (Q == { nib_g(A[15:12],B[15:12]),
                          nib_g(A[11:8], B[11:8]),
                          nib_g(A[7:4],  B[7:4]),
                          nib_g(A[3:0],  B[3:0]) });

  // Output/internal wiring consistency
  assert property (Q == result);
  assert property (Flags[1] == Q[15]);
  assert property (Flags[2] == (Q == 16'h0000));

  // Carry tree and Flags wiring
  assert property (Flags[0] == ~C_out[3]);
  assert property (C_out[0] == C[0]);
  assert property (C_out[1] == C[1] | (C[0] & ~Y[1]));
  assert property (C_out[2] == C[2] | (C[1] & ~Y[2]) | (C[0] & ~Y[1] & ~Y[2]));
  assert property (C_out[3] == C[3] | (C[2] & ~Y[3]) | (C[1] & ~Y[2] & ~Y[3]) | (C[0] & ~Y[1] & ~Y[2] & ~Y[3]));

  // Slice-side interface expectations given f=2'b00 in all slices
  assert property (X == {4{Op[1]}});  // h=c[0], c=Op[4:1]
  assert property (Y == 4'b0000);     // i=e & f[0], f[0]=0
  assert property (C[0] == 1'b1);     // j=~e|~f[1], f[1]=0
  assert property ((C[1] == 1'b1) && (C[2] == 1'b1) && (C[3] == 1'b1));
  assert property (C_out[3] == 1'b1);
  assert property (Flags[0] == 1'b0);

  // Q must not change on Op-only changes
  assert property ($stable(A) && $stable(B) && !$stable(Op) |-> $stable(Q));

  // Minimal functional coverage
  cover property (Q == 16'h0000 && Flags[2]);
  cover property (Q != 16'h0000 && !Flags[2]);
  cover property (Q[15] == 1'b0);
  cover property (Q[15] == 1'b1);
  cover property ($changed(Op));
  cover property (Op == 6'h00);
  cover property (Op == 6'h3F);
endmodule

module Circuit74181b_sva;
  event comb_ev; always @* -> comb_ev;
  default clocking @(comb_ev); endclocking

  function automatic [3:0] nib_g(input [3:0] a,b);
    logic [3:0] P,G;
    begin
      P = a & b;
      G = a | b;
      nib_g[0] = P[0];
      nib_g[1] = P[1] | (P[0] & G[1]);
      nib_g[2] = P[2] | (P[1] & G[2]) | (P[0] & G[1] & G[2]);
      nib_g[3] = P[3] | (P[2] & G[3]) | (P[1] & G[2] & G[3]) | (P[0] & G[1] & G[2] & G[3]);
    end
  endfunction

  // Core truth-table checks
  assert property (g == nib_g(a,b));
  assert property (h == c[0]);
  assert property (i == (e & f[0]));
  assert property (j == (~e | ~f[1]));

  // Minimal coverage
  cover property ($changed(a) || $changed(b));
  cover property (e && f[0]);
  cover property (!e && !f[1]);
  cover property (f[1] == 1'b0);
endmodule

// Bind checkers
bind BitsliceALU    BitsliceALU_sva    u_bitsliceALU_sva();
bind Circuit74181b  Circuit74181b_sva  u_74181b_sva();