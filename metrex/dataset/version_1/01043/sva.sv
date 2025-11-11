// SVA checker for shift_right
module shift_right_sva #(parameter A_SIGNED = 0, A_WIDTH = 32, Y_WIDTH = 32)
(
  input  logic [A_WIDTH-1:0] A,
  input  logic [4:0]         B,
  input  logic [A_WIDTH-1:0] Y
);

  // Elaboration-time sanity checks
  initial begin
    assert (A_WIDTH > 0) else $error("A_WIDTH must be > 0");
    assert (Y_WIDTH == A_WIDTH) else $error("Y_WIDTH != A_WIDTH (Y_WIDTH unused by DUT)");
    assert ($bits(B) == 5) else $error("B must be 5 bits");
    if (A_SIGNED != 0) $warning("A_SIGNED is unused by DUT; shift is logical (>>), not arithmetic (>>>)");
    if (A_WIDTH > 32)  $warning("A_WIDTH > 32 but B is 5 bits (max shift 31); larger shifts unreachable");
  end

  // Combinational functional correctness (bit-accurate, X-sensitive)
  always_comb begin
    // No-X propagation when inputs known
    if (!$isunknown({A,B})) assert (!$isunknown(Y)) else $error("Y has X/Z while inputs are known");

    // Zero shift equals passthrough
    if (B == 0) assert (Y === A) else $error("B==0 but Y!=A");

    // Bit-by-bit right-shift behavior for all B
    // For each output bit i:
    //   if (i+B < A_WIDTH) Y[i] must equal A[i+B]
    //   else               Y[i] must be 0
    for (int i = 0; i < A_WIDTH; i++) begin
      if (B < (A_WIDTH - i))
        assert (Y[i] === A[i+B]) else $error("Y[%0d] != A[%0d] for shift B=%0d", i, i+$unsigned(B), B);
      else
        assert (Y[i] == 1'b0)    else $error("Y[%0d] not zero when i+B >= A_WIDTH (B=%0d)", i, B);
    end
  end

  // Lightweight functional coverage (combinational sampling)
  always_comb begin
    cover (B == 0);
    cover (B == 1);
    cover (B == 31);
    if (A_WIDTH <= 32) cover (B == A_WIDTH-1);
    cover (B >= A_WIDTH); // expect zero output when true
    cover (A == '0);
    cover (A == '1);
    cover (A[A_WIDTH-1] && (B > 0));
  end

endmodule

// Bind into DUT
bind shift_right shift_right_sva #(.A_SIGNED(A_SIGNED), .A_WIDTH(A_WIDTH), .Y_WIDTH(Y_WIDTH))
  shift_right_sva_i (.A(A), .B(B), .Y(Y));