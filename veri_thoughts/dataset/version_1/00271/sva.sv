// SVA for xor_32
module xor_32_sva (input [31:0] a, b, input [31:0] out);

  // Functional correctness (4-state accurate)
  always_comb
    assert (out === (a ^ b))
      else $error("xor_32 mismatch: a=%h b=%h out=%h", a, b, out);

  // X-propagation: known inputs => known output
  always_comb
    if (!$isunknown({a,b}))
      assert (!$isunknown(out))
        else $error("xor_32 X-prop error: a=%h b=%h out=%h", a, b, out);

  // Per-bit functional coverage of all input combinations
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : g_cov
      always_comb begin
        cover (a[i]==0 && b[i]==0 && out[i]==0);
        cover (a[i]==0 && b[i]==1 && out[i]==1);
        cover (a[i]==1 && b[i]==0 && out[i]==1);
        cover (a[i]==1 && b[i]==1 && out[i]==0);
      end
      // Toggle coverage per bit
      cover property (@(posedge out[i]) 1'b1);
      cover property (@(negedge out[i]) 1'b1);
    end
  endgenerate

  // Vector-level corner coverage
  always_comb begin
    cover ((a == b)  && (out == '0));
    cover ((a == ~b) && (out == ~'0));
  end

endmodule

bind xor_32 xor_32_sva sva_xor_32 (.*);