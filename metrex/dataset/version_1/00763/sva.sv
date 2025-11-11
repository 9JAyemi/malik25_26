// SVA checker for comb_circuit
// Bind this module to the DUT to verify functionality and provide coverage.
module comb_circuit_sva;

  // Pairwise gate checks
  genvar i;
  generate
    for (i = 0; i < 50; i++) begin : chk_pairs
      always_comb begin
        assert (and_out[i] === (in[2*i] & in[2*i+1]))
          else $error("comb_circuit and_out[%0d] mismatch", i);
        assert (or_out[i]  === (in[2*i] | in[2*i+1]))
          else $error("comb_circuit or_out[%0d] mismatch", i);
      end
    end
    for (i = 0; i < 99; i++) begin : chk_xor_chain
      always_comb begin
        assert (xor_out[i] === (in[i] ^ in[i+1]))
          else $error("comb_circuit xor_out[%0d] mismatch", i);
      end
    end
  endgenerate

  // Reduction output checks (functional equivalence)
  always_comb begin
    // Out equals reductions of inputs
    assert (out_and === (&in)) else $error("comb_circuit out_and != &in");
    assert (out_or  === (|in)) else $error("comb_circuit out_or  != |in");
    // XOR telescopes to end bits; also equals reduction of xor_out
    assert (out_xor === (in[0] ^ in[99])) else $error("comb_circuit out_xor != in[0]^in[99]");
    assert (out_xor === (^xor_out))       else $error("comb_circuit out_xor != ^xor_out");
    // Out equals reductions of intermediate vectors
    assert (out_and === (&and_out)) else $error("comb_circuit out_and != &and_out");
    assert (out_or  === (|or_out))  else $error("comb_circuit out_or  != |or_out");

    // Knownness: with known inputs, all internal/outputs must be known
    if (!$isunknown(in)) begin
      assert (!$isunknown({and_out,or_out,xor_out,out_and,out_or,out_xor}))
        else $error("comb_circuit X/Z on internal/output with known inputs");
    end
  end

  // Lightweight coverage
  always_comb begin
    // Output value coverage
    cover (out_and == 0); cover (out_and == 1);
    cover (out_or  == 0); cover (out_or  == 1);
    cover (out_xor == 0); cover (out_xor == 1);
    // Corner patterns
    cover (~|in);    // all zeros
    cover (&in);     // all ones
    cover (in[0] ^ in[99]); // XOR end-bits = 1 case
  end

  // Per-pair input combination coverage (all 4 combos per pair)
  generate
    for (i = 0; i < 50; i++) begin : cov_pairs
      always_comb begin
        cover ({in[2*i],in[2*i+1]} == 2'b00);
        cover ({in[2*i],in[2*i+1]} == 2'b01);
        cover ({in[2*i],in[2*i+1]} == 2'b10);
        cover ({in[2*i],in[2*i+1]} == 2'b11);
      end
    end
  endgenerate

endmodule

bind comb_circuit comb_circuit_sva sva_i();