// SVA checker for blake2_G (concise, full functional equivalence + key coverage)
module blake2_G_sva (blake2_G dut);

  function automatic logic [63:0] rol64 (input logic [63:0] x, input int unsigned n);
    return (x << n) | (x >> (64 - n));
  endfunction

  logic [63:0] a0_ref, d1_ref, c0_ref, b1_ref, a1_ref, d3_ref, c1_ref, b3_ref;

  always_comb begin
    a0_ref = dut.a + dut.b + dut.m0;
    d1_ref = rol64(dut.d ^ a0_ref, 32);
    c0_ref = dut.c + d1_ref;
    b1_ref = rol64(dut.b ^ c0_ref, 24);
    a1_ref = a0_ref + b1_ref + dut.m1;
    d3_ref = rol64(d1_ref ^ a1_ref, 16);
    c1_ref = c0_ref + d3_ref;
    b3_ref = rol64(b1_ref ^ c1_ref, 1);
  end

  // Functional equivalence (purely combinational, immediate assertions)
  always_comb begin
    assert (dut.a_prim === a1_ref)
      else $error("blake2_G a_prim mismatch: got %h exp %h", dut.a_prim, a1_ref);
    assert (dut.b_prim === b3_ref)
      else $error("blake2_G b_prim mismatch: got %h exp %h", dut.b_prim, b3_ref);
    assert (dut.c_prim === c1_ref)
      else $error("blake2_G c_prim mismatch: got %h exp %h", dut.c_prim, c1_ref);
    assert (dut.d_prim === d3_ref)
      else $error("blake2_G d_prim mismatch: got %h exp %h", dut.d_prim, d3_ref);

    // X-propagation: known inputs imply known outputs
    if (!$isunknown({dut.a,dut.b,dut.c,dut.d,dut.m0,dut.m1})) begin
      assert (!$isunknown({dut.a_prim,dut.b_prim,dut.c_prim,dut.d_prim}))
        else $error("blake2_G produced X/Z on outputs with known inputs");
    end

    // Minimal but meaningful coverage
    // - exercise wrap-around carry in both additions
    cover ( (dut.a + dut.b + dut.m0) < dut.a );
    cover ( a1_ref < a0_ref );
    // - ensure rotate paths see boundary 1-bits
    cover ( (dut.d ^ a0_ref)[63] );                 // affects 32-bit rotate boundary
    cover ( (rol64(dut.b ^ c0_ref,24))[63] );       // affects 24-bit rotate boundary
    cover ( (b1_ref ^ c1_ref)[63] );                // affects 1-bit rotate boundary
  end

endmodule

bind blake2_G blake2_G_sva sva_i();