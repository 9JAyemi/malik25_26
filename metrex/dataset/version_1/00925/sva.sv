// SVA checkers and binds for the provided design

// XOR_module checker
module xor_module_comb_sva(input logic [7:0] A, B, input logic [7:0] out);
  // Functional correctness
  always_comb begin
    assert (out == (A ^ B))
      else $error("XOR_module: out != A ^ B");
    // If inputs are known, output must be known
    assert ($isunknown({A,B}) || !$isunknown(out))
      else $error("XOR_module: X/Z on out with known inputs");
    // Idempotence: A==B => out==0
    assert ((A==B) ? (out=='0) : 1)
      else $error("XOR_module: A==B but out!=0");
  end

  // Coverage (exercise each bit and a few patterns)
  genvar i;
  generate for (i=0;i<8;i++) begin : gen_cov_bit
    always_comb cover (out[i]);
  end endgenerate
  always_comb begin
    cover (A==B);                     // hits idempotence case
    cover (A==8'h00 && B==8'h00);
    cover (A==8'hFF && B==8'h00);
    cover (A==8'hAA && B==8'h55);
  end
endmodule

// OR_module checker
module or_module_comb_sva(input logic in1, in2, input logic out);
  always_comb begin
    assert (out == (in1 | in2))
      else $error("OR_module: out != in1 | in2");
    assert ($isunknown({in1,in2}) || !$isunknown(out))
      else $error("OR_module: X/Z on out with known inputs");
  end
  always_comb begin
    cover (out==1'b0);
    cover (out==1'b1);
  end
endmodule

// top_module checker (connectivity + end-to-end)
module top_module_comb_sva(
  input logic [7:0] A, B,
  input logic [7:0] XOR_out,
  input logic       OR_out
);
  always_comb begin
    // End-to-end XOR correctness
    assert (XOR_out == (A ^ B))
      else $error("top: XOR_out != A ^ B");
    // OR wiring correctness from XOR_out[1:0]
    assert (OR_out == (XOR_out[0] | XOR_out[1]))
      else $error("top: OR_out != XOR_out[0] | XOR_out[1]");
    // End-to-end OR correctness from A/B directly
    assert (OR_out == ((A[0]^B[0]) | (A[1]^B[1])))
      else $error("top: OR_out inconsistent with A/B");
    // No X/Z on outputs when inputs known
    assert ($isunknown({A,B}) || !$isunknown({XOR_out,OR_out}))
      else $error("top: X/Z on outputs with known inputs");
  end

  // Coverage of OR input combinations via XOR_out[1:0]
  always_comb begin
    cover (XOR_out[1:0]==2'b00);
    cover (XOR_out[1:0]==2'b01);
    cover (XOR_out[1:0]==2'b10);
    cover (XOR_out[1:0]==2'b11);
  end
endmodule

// Bind checkers to DUT
bind XOR_module xor_module_comb_sva xor_chk (.*);
bind OR_module  or_module_comb_sva  or_chk  (.*);
bind top_module top_module_comb_sva top_chk (.*);