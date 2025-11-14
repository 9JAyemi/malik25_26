// SVA for add_4bit_sat
// Binds to every instance and checks saturating add: Y = min(A+B, 15)

module add_4bit_sat_sva (input logic [3:0] A, B, input logic [3:0] Y);
  logic [4:0] sum5 = {1'b0, A} + {1'b0, B};

  // Exact result when no overflow
  property p_no_overflow_exact;
    @(A or B) disable iff ($isunknown({A,B}))
      (sum5 <= 5'd15) |-> ##0 (Y == sum5[3:0] && !$isunknown(Y));
  endproperty
  assert property (p_no_overflow_exact)
    else $error("Non-overflow result must be exact: A=%0h B=%0h Y=%0h", A,B,Y);

  // Saturate on overflow
  property p_overflow_saturates;
    @(A or B) disable iff ($isunknown({A,B}))
      (sum5 > 5'd15) |-> ##0 (Y == 4'hF && !$isunknown(Y));
  endproperty
  assert property (p_overflow_saturates)
    else $error("Overflow must saturate to 0xF: A=%0h B=%0h Y=%0h", A,B,Y);

  // No X/Z on output when inputs are known
  property p_no_x_out;
    @(A or B) disable iff ($isunknown({A,B})) ##0 !$isunknown(Y);
  endproperty
  assert property (p_no_x_out)
    else $error("Y unknown with known inputs: A=%0h B=%0h Y=%0h", A,B,Y);

  // Functional coverage
  cover property (@(A or B) ! $isunknown({A,B}) && (sum5 <= 5'd15) && (Y == sum5[3:0]));
  cover property (@(A or B) ! $isunknown({A,B}) && (sum5 >  5'd15) && (Y == 4'hF));

  // Corner cases
  cover property (@(A or B) A==4'h0 && B==4'h0 && Y==4'h0); // min
  cover property (@(A or B) A==4'h7 && B==4'h8 && Y==4'hF); // boundary exact 15
  cover property (@(A or B) A==4'h8 && B==4'h8 && Y==4'hF); // overflow saturate
  cover property (@(A or B) A==4'hF && B==4'h0 && Y==4'hF); // max + 0
  cover property (@(A or B) A==4'hF && B==4'h1 && Y==4'hF); // max + 1 overflow
endmodule

bind add_4bit_sat add_4bit_sat_sva sva (.*);