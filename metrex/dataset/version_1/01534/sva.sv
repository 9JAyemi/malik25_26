// SVA bind module for zero_detect_owire
module zero_detect_owire_sva;
  // Access DUT internals via bind: in, out, zero_found

  // Combinational correctness and X-checks
  always_comb begin
    // Internal signal must implement OR-reduction of input
    assert (zero_found === (|in))
      else $error("zero_found != |in  zero_found=%b in=%b", zero_found, in);

    // Output must be the inverse of zero_found
    assert (out === ~zero_found)
      else $error("out != ~zero_found  out=%b zero_found=%b", out, zero_found);

    // Direct functional equivalence
    assert (out === ~(|in))
      else $error("out != ~(|in)  out=%b in=%b", out, in);

    // With known inputs, outputs must be known
    if (!$isunknown(in)) begin
      assert (!$isunknown(zero_found))
        else $error("zero_found X/Z with known in  in=%b zero_found=%b", in, zero_found);
      assert (!$isunknown(out))
        else $error("out X/Z with known in  in=%b out=%b", in, out);
    end
  end

  // Functional coverage (key use-cases)
  always_comb begin
    cover (in == 4'h0 && out == 1'b1);          // all-zero input detected
    cover (in != 4'h0 && out == 1'b0);          // non-zero input not detected
    cover ($onehot(in) && out == 1'b0);         // single-bit set
    cover ((in & (in - 1)) != 0 && out == 1'b0);// multi-bit set
    cover (in == 4'hF && out == 1'b0);          // all ones
  end
endmodule

bind zero_detect_owire zero_detect_owire_sva sva_i();