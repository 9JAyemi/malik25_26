// SVA checker for modifiedBooth. Bind this to the DUT.
// Focus: functional correctness, X-propagation, key bit check, and concise coverage.

module modifiedBooth_sva;

  // Bound into modifiedBooth scope; can reference A, B, out, rC1/2/3, rT1/2 directly.

  // Small free-running sampling clock for concurrent assertions/coverage
  bit sva_clk = 0;
  initial sva_clk = 0;
  always #1 sva_clk = ~sva_clk;

  default clocking cb @(posedge sva_clk); endclocking

  // Combinational immediate check (strongest: checks at every delta)
  always @* begin
    if (!$isunknown({A,B})) begin
      assert (out == (A * B))
        else $error("modifiedBooth product mismatch: A=%0h B=%0h out=%0h exp=%0h",
                    A, B, out, (A*B));
    end
  end

  // Concurrent assertions (sampled)
  // Known inputs imply known internal temps and outputs
  assert property (!$isunknown({A,B}) |-> !$isunknown({out, rC1, rC2, rC3, rT1, rT2}))
    else $error("modifiedBooth X/Z propagation with known inputs");

  // Basic identity/zero properties
  assert property ((A==0 || B==0) |-> (out==0))
    else $error("Zero multiplicand violated");
  assert property ((A==1) |-> (out==B))
    else $error("Identity (A==1) violated");
  assert property ((B==1) |-> (out==A))
    else $error("Identity (B==1) violated");

  // Bit-0 structural check (sanity guard)
  assert property (out[0] == (A[0] & B[0]))
    else $error("LSB mismatch: A0&B0 != out[0]");

  // Main functional equivalence (sampled)
  assert property (out == (A * B))
    else $error("Sampled product mismatch: A=%0h B=%0h out=%0h exp=%0h",
                A, B, out, (A*B));

  // Targeted functional coverage
  cover property (A==0 && B==0 && out==0);                    // all zero
  cover property (A==4'hF && B==4'hF && out==8'hE1);          // max*max
  cover property (A==4'hF && B==0    && out==0);              // max*0
  cover property (A==0    && B==4'hF && out==0);              // 0*max
  cover property (A==1 && out==B);                            // identity A
  cover property (B==1 && out==A);                            // identity B
  cover property (A==4'h8 && B==4'h8 && out==8'h40);          // MSB*MSB

  // Carry activity coverage (ensures adder paths exercised)
  cover property (rC1);
  cover property (rC2);
  cover property (rC3);

  // Output bit toggle coverage
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_out_toggles
      cover property ($rose(out[i]));
      cover property ($fell(out[i]));
    end
  endgenerate

endmodule

bind modifiedBooth modifiedBooth_sva u_modifiedBooth_sva();