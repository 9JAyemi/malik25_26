// SVA for expand_key_type_B_256 and S4
// Concise, functionally complete, combinational checks with minimal coverage

// Checker bound into expand_key_type_B_256
module expand_key_type_B_256_sva;
  // Golden S4 function
  function automatic logic [31:0] s4f (input logic [31:0] x);
    return x ^ (x << 11) ^ (x << 22);
  endfunction

  always_comb begin
    // Decompose input words
    logic [31:0] k0 = in[255:224];
    logic [31:0] k1 = in[223:192];
    logic [31:0] k2 = in[191:160];
    logic [31:0] k3 = in[159:128];
    logic [31:0] k4 = in[127:96];
    logic [31:0] k5 = in[95:64];
    logic [31:0] k6 = in[63:32];
    logic [31:0] k7 = in[31:0];

    // Derived values
    logic [31:0] v5 = k4 ^ k5;
    logic [31:0] v6 = v5 ^ k6;
    logic [31:0] v7 = v6 ^ k7;
    logic [31:0] k8 = s4f(k3);

    // Golden outputs
    logic [255:0] out1_g = {k0, k1, k2, k3,
                            (k4 ^ k8),
                            (v5 ^ k8),
                            (v6 ^ k8),
                            (v7 ^ k8)};
    logic [127:0] out2_g = out1_g[127:0];

    // Functional equivalence
    assert (out_1 === out1_g)
      else $error("expand_key_type_B_256: out_1 mismatch");

    assert (out_2 === out2_g)
      else $error("expand_key_type_B_256: out_2 mismatch");

    // Internal instance S4_0 correctness
    assert (S4_0.out === s4f(S4_0.in))
      else $error("expand_key_type_B_256: S4_0 output mismatch");

    // Consistency: out_2 mirrors lower half of out_1
    assert (out_2 === out_1[127:0])
      else $error("expand_key_type_B_256: out_2 != out_1[127:0]");

    // Knownness: no X/Z on outputs if input is known
    if (!$isunknown(in)) begin
      assert (!$isunknown({out_1, out_2}))
        else $error("expand_key_type_B_256: X/Z on outputs with known input");
    end

    // Minimal coverage
    cover (s4f(k3) == 32'h0);
    cover (s4f(k3) != 32'h0);
    cover (v5 == 32'h0);
    cover (v6 == 32'h0);
    cover (v7 == 32'h0);
    cover (out_2 == 128'h0);
    cover (out_2 != 128'h0);
  end
endmodule

// Checker bound into S4 for standalone instances (if any)
module S4_sva;
  function automatic logic [31:0] s4f (input logic [31:0] x);
    return x ^ (x << 11) ^ (x << 22);
  endfunction
  always_comb begin
    assert (out === s4f(in))
      else $error("S4: functional mismatch");
    if (!$isunknown(in)) begin
      assert (!$isunknown(out))
        else $error("S4: X/Z on out with known in");
    end
    // Minimal coverage
    cover (in == 32'h0);
    cover (in == 32'h1);
    cover (in[31] && !in[0]);
  end
endmodule

// Bind statements
bind expand_key_type_B_256 expand_key_type_B_256_sva chk_exB256();
bind S4                    S4_sva                    chk_S4();