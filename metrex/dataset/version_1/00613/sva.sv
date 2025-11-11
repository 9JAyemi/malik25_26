// SVA for full_adder and adder_4bit
// Bind these into the DUT; no DUT/testbench code modified.

`ifndef SYNTHESIS

// ---------------- full_adder assertions ----------------
module full_adder_sva(input a, input b, input carry_in, input sum, input carry_out);

  // Functional equivalence
  assert property (@(a or b or carry_in or sum or carry_out)
                   sum == (a ^ b ^ carry_in))
    else $error("full_adder sum mismatch");

  assert property (@(a or b or carry_in or sum or carry_out)
                   carry_out == ((a & b) | (a & carry_in) | (b & carry_in)))
    else $error("full_adder carry_out mismatch");

  // Derived behavior: generate/kill/propagate
  assert property (@(a or b or carry_in or sum or carry_out)
                   (a & b) |-> carry_out)
    else $error("full_adder generate violated");

  assert property (@(a or b or carry_in or sum or carry_out)
                   (~a & ~b) |-> !carry_out)
    else $error("full_adder kill violated");

  assert property (@(a or b or carry_in or sum or carry_out)
                   (a ^ b) |-> (carry_out == carry_in))
    else $error("full_adder propagate violated");

  // No X on outputs
  assert property (@(a or b or carry_in or sum or carry_out)
                   !$isunknown({sum,carry_out}))
    else $error("full_adder X/Z on outputs");

  // Truth-table coverage (all 8 input combinations)
  cover property (@(a or b or carry_in) (~a & ~b & ~carry_in));
  cover property (@(a or b or carry_in) (~a & ~b &  carry_in));
  cover property (@(a or b or carry_in) (~a &  b & ~carry_in));
  cover property (@(a or b or carry_in) (~a &  b &  carry_in));
  cover property (@(a or b or carry_in) ( a & ~b & ~carry_in));
  cover property (@(a or b or carry_in) ( a & ~b &  carry_in));
  cover property (@(a or b or carry_in) ( a &  b & ~carry_in));
  cover property (@(a or b or carry_in) ( a &  b &  carry_in));

endmodule

bind full_adder full_adder_sva fa_sva_i(.*);

// ---------------- adder_4bit assertions ----------------
module adder4_sva(
  input  [3:0] A,
  input  [3:0] B,
  input  [4:0] C,
  input  [3:0] sum,     // internal from DUT
  input  [4:0] carry    // internal from DUT
);

  // End-to-end correctness
  assert property (@(A or B or C) C == (A + B))
    else $error("adder_4bit C != A+B");

  // Output composition matches internal signals
  assert property (@(sum or carry or C) C == {carry[4], sum})
    else $error("adder_4bit C packing mismatch");

  // LSB stage (cin=0)
  assert property (@(A[0] or B[0] or sum[0] or carry[1])
                   sum[0] == (A[0] ^ B[0]))
    else $error("adder_4bit bit0 sum mismatch");

  assert property (@(A[0] or B[0] or carry[1])
                   carry[1] == (A[0] & B[0]))
    else $error("adder_4bit bit0 carry mismatch");

  // Stages 1..3: full-adder equations and propagate behavior
  genvar i;
  generate
    for (i = 1; i < 4; i++) begin : g_fa_eqs
      assert property (@(A[i] or B[i] or carry[i] or sum[i])
                       sum[i] == (A[i] ^ B[i] ^ carry[i]))
        else $error("adder_4bit bit%0d sum mismatch", i);

      assert property (@(A[i] or B[i] or carry[i] or carry[i+1])
                       carry[i+1] == ((A[i] & B[i]) | (A[i] & carry[i]) | (B[i] & carry[i])))
        else $error("adder_4bit bit%0d carry mismatch", i);

      assert property (@(A[i] or B[i] or carry[i] or carry[i+1])
                       (A[i] ^ B[i]) |-> (carry[i+1] == carry[i]))
        else $error("adder_4bit bit%0d propagate violated", i);
    end
  endgenerate

  // No X on observable outputs and key internals (exclude carry[0], undriven)
  assert property (@(A or B or C or sum or carry)
                   !$isunknown(C))
    else $error("adder_4bit X/Z on C");

  assert property (@(sum) !$isunknown(sum))
    else $error("adder_4bit X/Z on sum");

  assert property (@(carry) !$isunknown(carry[4:1]))
    else $error("adder_4bit X/Z on carry[4:1]");

  // Minimal but meaningful coverage
  cover property (@(A or B or C) (C[4] == 0)); // no overflow
  cover property (@(A or B or C) (C[4] == 1)); // overflow

  // Per-stage generate/kill/propagate coverage
  generate
    for (i = 1; i < 4; i++) begin : g_cov
      cover property (@(A[i] or B[i]) (A[i] & B[i]));          // generate
      cover property (@(A[i] or B[i]) (~A[i] & ~B[i]));        // kill
      cover property (@(A[i] or B[i] or carry[i]) ((A[i]^B[i]) &  carry[i])); // propagate 1
      cover property (@(A[i] or B[i] or carry[i]) ((A[i]^B[i]) & ~carry[i])); // propagate 0
    end
  endgenerate

endmodule

bind adder_4bit adder4_sva a4_sva_i(.A(A), .B(B), .C(C), .sum(sum), .carry(carry));

`endif