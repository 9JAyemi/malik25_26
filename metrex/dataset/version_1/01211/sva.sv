// SVA checker for my_logic_op
module my_logic_op_sva (
  input  logic [2:0] in,
  input  logic       out,
  input  logic       and0_out, and1_out, and2_out,
  input  logic       or0_out,  or1_out,
  input  logic       not0_out, not1_out, not2_out,
  input  logic       xor0_out, xor1_out, xor2_out, xor3_out, xor4_out, xor5_out, xor6_out
);

  // No X/Z on any observed signals
  always_comb begin
    assert (!$isunknown({in, and0_out, and1_out, and2_out, or0_out, or1_out,
                         not0_out, not1_out, not2_out, xor0_out, xor1_out,
                         xor2_out, xor3_out, xor4_out, xor5_out, xor6_out, out}))
      else $error("my_logic_op: X/Z detected on inputs/ints/out");
  end

  // Primitive-gate equivalences
  always_comb begin
    // ANDs
    assert #0 (and0_out == (in[0] & in[1]));
    assert #0 (and1_out == (in[0] & in[2]));
    assert #0 (and2_out == (in[1] & in[2]));
    // XORs
    assert #0 (xor0_out == (in[0] ^ in[1]));
    assert #0 (xor1_out == (in[0] ^ in[2]));
    assert #0 (xor2_out == (in[1] ^ in[2]));
    assert #0 (xor3_out == (xor0_out ^ in[2]));
    assert #0 (xor4_out == (xor1_out ^ in[1]));
    assert #0 (xor5_out == (xor2_out ^ in[0]));
    assert #0 (xor6_out == (xor3_out ^ xor4_out ^ xor5_out));
    // ORs
    assert #0 (or0_out  == (and0_out | and1_out));
    assert #0 (or1_out  == (or0_out | and2_out | xor6_out));
    // NOTs
    assert #0 (not0_out == ~in[0]);
    assert #0 (not1_out == ~in[1]);
    assert #0 (not2_out == ~in[2]);
  end

  // Useful simplifications/functional checks
  always_comb begin
    assert #0 (xor6_out == ^in);         // parity of 3 inputs
    assert #0 (or1_out  == (|in));       // reduces to input OR
    assert #0 (out      == ~(and0_out | and1_out | and2_out)); // <=1 ones
    assert #0 (out      == ($countones(in) <= 1));
  end

  // Coverage: all input combinations and key internal/output states
  always_comb begin
    cover (in == 3'b000);
    cover (in == 3'b001);
    cover (in == 3'b010);
    cover (in == 3'b011);
    cover (in == 3'b100);
    cover (in == 3'b101);
    cover (in == 3'b110);
    cover (in == 3'b111);

    cover (out == 1'b1);
    cover (out == 1'b0);

    cover (xor6_out);   cover (!xor6_out);
    cover (or1_out);    cover (!or1_out);
    cover (and0_out);   cover (and1_out);   cover (and2_out);
  end

endmodule

// Bind into all instances of my_logic_op
bind my_logic_op my_logic_op_sva my_logic_op_sva_i (.*);