// SVA checker for adder32
// Binds to DUT and verifies functionality and key corner-case coverage.
// Concise: primary functional equivalence, X-prop checks, carry-chain, and coverage.

module adder32_sva (adder32 dut);

  // Use a global sampling clock for concurrent SVA on a combinational DUT
  default clocking cb @ (posedge $global_clock); endclocking

  // Vectorize ports
  logic [15:0] A, B, S;
  assign A = {dut.a15,dut.a14,dut.a13,dut.a12,dut.a11,dut.a10,dut.a9,dut.a8,
              dut.a7,dut.a6,dut.a5,dut.a4,dut.a3,dut.a2,dut.a1,dut.a0};
  assign B = {dut.b15,dut.b14,dut.b13,dut.b12,dut.b11,dut.b10,dut.b9,dut.b8,
              dut.b7,dut.b6,dut.b5,dut.b4,dut.b3,dut.b2,dut.b1,dut.b0};
  assign S = {dut.s15,dut.s14,dut.s13,dut.s12,dut.s11,dut.s10,dut.s9,dut.s8,
              dut.s7,dut.s6,dut.s5,dut.s4,dut.s3,dut.s2,dut.s1,dut.s0};

  // Reference sum and expected carry chain (no external carry-in)
  logic [16:0] ref_sum;
  assign ref_sum = A + B;

  logic [16:0] c_exp;
  integer k;
  always_comb begin
    c_exp[0] = 1'b0;
    for (k = 0; k < 16; k++) begin
      c_exp[k+1] = (A[k] & B[k]) | (A[k] & c_exp[k]) | (B[k] & c_exp[k]);
    end
  end

  // X-propagation guard: when inputs are known, outputs must be known
  a_no_x_on_outputs: assert property ( !$isunknown({A,B}) |-> !$isunknown({dut.cout,S}) );

  // Functional equivalence: outputs represent A+B
  a_sum_matches_add: assert property ( !$isunknown({A,B}) |-> {dut.cout,S} == ref_sum );

  // Carry-out equivalence to ripple chain (pinpoints carry-chain bugs)
  a_cout_ripple: assert property ( !$isunknown({A,B}) |-> dut.cout == c_exp[16] );

  // Per-bit sum = a^b^carry_in (concise pinpointing across bits)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_bit
      a_bit_xor_cin: assert property ( !$isunknown({A,B}) |-> S[i] == (A[i] ^ B[i] ^ c_exp[i]) );
    end
  endgenerate

  // Corner-case and structural coverage
  c_zero_plus_zero:     cover property ( A == 16'h0000 && B == 16'h0000 );
  c_alt_no_carry:       cover property ( A == 16'hAAAA && B == 16'h5555 && dut.cout == 1'b0 );
  c_full_ripple_chain:  cover property ( A == 16'hFFFF && B == 16'h0001 && dut.cout == 1'b1 );
  c_any_overflow:       cover property ( dut.cout == 1'b1 );
  c_no_overflow:        cover property ( dut.cout == 1'b0 );

  // Exercise carry behaviors at each bit: generate, propagate-with-cin, and kill-with-cin
  generate
    for (i = 0; i < 16; i++) begin : g_cov
      c_gen_at_bit:     cover property ( A[i] & B[i] );                           // generate
      c_prop_at_bit:    cover property ( c_exp[i] && (A[i] ^ B[i]) );             // propagate
      c_kill_at_bit:    cover property ( c_exp[i] && ~A[i] && ~B[i] );            // kill
    end
  endgenerate

endmodule

// Bind into all adder32 instances
bind adder32 adder32_sva sva_adder32_chk();