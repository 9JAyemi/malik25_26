// SVA for addition_module
module addition_module_sva (
  input logic [7:0] A,
  input logic [7:0] B,
  input logic [8:0] Sum
);

  // Functional correctness: 9-bit sum must equal zero-extended A+B when inputs are known
  a_sum_correct: assert property ( $isunknown({A,B}) or
                                   (Sum == ({1'b0, A} + {1'b0, B})) )
    else $error("Sum mismatch: expected %0d, got %0d", ({1'b0,A}+{1'b0,B}), Sum);

  // No spurious output toggles without input change
  a_no_spurious_toggle: assert property ( $changed(Sum) |-> ($changed(A) || $changed(B)) )
    else $error("Sum changed without A or B changing");

  // Coverage: hit both carry/no-carry and key edge cases
  c_no_carry:  cover property ( !$isunknown({A,B,Sum}) && (Sum[8] == 1'b0) );
  c_with_carry:cover property ( !$isunknown({A,B,Sum}) && (Sum[8] == 1'b1) );
  c_zero:      cover property ( A==8'h00 && B==8'h00 && Sum==9'h000 );
  c_max:       cover property ( A==8'hFF && B==8'hFF && Sum==9'h1FE );
  c_boundary1: cover property ( A==8'hFF && B==8'h01 && Sum==9'h100 );

endmodule

// Bind into DUT
bind addition_module addition_module_sva dut_sva (.A(A), .B(B), .Sum(Sum));