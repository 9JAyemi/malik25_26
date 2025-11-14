// SVA for adder32 (16-bit ripple-carry adder with cout)
// Bind this checker to the DUT:  bind adder32 adder32_sva u_adder32_sva(.*);

module adder32_sva (
  input logic a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,
  input logic b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,
  input logic s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,
  input logic cout
);

  // Pack ports into vectors for concise checks
  logic [15:0] A, B, S;
  assign A = {a15,a14,a13,a12,a11,a10,a9,a8,a7,a6,a5,a4,a3,a2,a1,a0};
  assign B = {b15,b14,b13,b12,b11,b10,b9,b8,b7,b6,b5,b4,b3,b2,b1,b0};
  assign S = {s15,s14,s13,s12,s11,s10,s9,s8,s7,s6,s5,s4,s3,s2,s1,s0};

  function automatic logic maj3(logic x,y,z);
    return (x&y)|(x&z)|(y&z);
  endfunction

  // Carry at bit index idx (c[0]=0, returns c[idx])
  function automatic logic carry_at(input int idx);
    logic c; c = 1'b0;
    for (int j = 0; j < idx; j++) c = maj3(A[j], B[j], c);
    return c;
  endfunction

  // Combinational, X-safe checks and concise coverage
  always_comb begin
    if (!$isunknown({A,B})) begin
      // End-to-end functional equivalence (primary check)
      assert ({cout,S} == ({1'b0,A} + {1'b0,B}))
        else $error("adder32 sum/carry mismatch: A=%h B=%h got={%b,%h} exp=%h",
                    A,B,cout,S,({1'b0,A}+{1'b0,B}));

      // Bitwise sum-of-three with correct carry-in
      for (int i = 0; i < 16; i++) begin
        assert (S[i] == (A[i] ^ B[i] ^ carry_at(i)))
          else $error("adder32 S[%0d] mismatch: Ai=%b Bi=%b Cin=%b So=%b",
                      i, A[i], B[i], carry_at(i), S[i]);
      end

      // Optional sanity: no X on outputs when inputs are 2-state
      assert (!$isunknown({cout,S}))
        else $error("adder32 produced X/Z outputs for 2-state inputs A=%h B=%h", A, B);
    end

    // Concise functional coverage
    // Basic zero case
    cover (! $isunknown({A,B,cout,S}) && A==16'h0000 && B==16'h0000 && S==16'h0000 && cout==1'b0);
    // Longest propagate chain (ripple through all bits)
    cover (! $isunknown({A,B,cout,S}) && A==16'hFFFF && B==16'h0001 && S==16'h0000 && cout==1'b1);
    // No-carry pairwise (alternating bits)
    cover (! $isunknown({A,B,cout,S}) && A==16'hAAAA && B==16'h5555 && S==16'hFFFF && cout==1'b0);
    // Any overflow
    cover (! $isunknown({A,B,cout,S}) && cout==1'b1);
    // Local 4-bit ripple example (lower nibble propagate, stop at bit4)
    cover (! $isunknown({A,B,cout,S}) && A==16'h000F && B==16'h0001 && S==16'h0010 && cout==1'b0);
  end

endmodule

// Bind into DUT (connects by port name). Place in a separate file or after DUT.
bind adder32 adder32_sva u_adder32_sva (.*);