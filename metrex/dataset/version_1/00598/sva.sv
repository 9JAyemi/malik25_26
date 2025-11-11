// SVA for bitwise_and
module bitwise_and_sva (input logic [3:0] A, B, input logic [3:0] Y);

  // Functional equivalence (allow delta-cycle for comb update)
  property p_and_vec;
    @(A or B or Y) 1'b1 |-> ##0 (Y === (A & B));
  endproperty
  assert property (p_and_vec)
    else $error("bitwise_and mismatch: A=%0h B=%0h Y=%0h exp=%0h", A, B, Y, (A & B));

  // No-X on output when inputs are known (per bit)
  genvar i;
  for (i = 0; i < 4; i++) begin : bit_checks
    property p_no_x;
      @(A[i] or B[i] or Y[i]) !$isunknown({A[i], B[i]}) |-> ##0 !$isunknown(Y[i]);
    endproperty
    assert property (p_no_x)
      else $error("Y[%0d] unknown with known inputs: A=%b B=%b Y=%b", i, A[i], B[i], Y[i]);

    // Per-bit functional coverage: drive 1 and 0
    cover property (@(A[i] or B[i] or Y[i]) ##0 (A[i] && B[i] && Y[i])); // Y[i]=1 case
    cover property (@(A[i] or B[i] or Y[i]) ##0 ((!A[i] || !B[i]) && !Y[i])); // Y[i]=0 case
  end

  // Vector-level functional coverage
  cover property (@(A or B or Y) ##0 (Y == 4'h0));
  cover property (@(A or B or Y) ##0 (Y == 4'hF));
  cover property (@(A or B or Y) ##0 $onehot(Y));
  cover property (@(A or B or Y) ##0 ($countones(Y) == 2));

endmodule

// Bind into DUT
bind bitwise_and bitwise_and_sva sva_inst (.A(A), .B(B), .Y(Y));