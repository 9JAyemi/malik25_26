// SVA for adder_with_overflow_detection
module adder_with_overflow_detection_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       Cin,
  input logic [3:0] Sum,
  input logic       Cout
);

  function automatic [4:0] full_sum(input logic [3:0] a, b, input logic cin);
    full_sum = {1'b0,a} + {1'b0,b} + cin;
  endfunction

  // Functional correctness (5-bit sum must match)
  ap_func: assert property (@(A or B or Cin)
    !$isunknown({A,B,Cin}) |-> ##0 {Cout,Sum} == full_sum(A,B,Cin));

  // Carry-out definition
  ap_cout: assert property (@(A or B or Cin)
    !$isunknown({A,B,Cin}) |-> ##0 Cout == (full_sum(A,B,Cin) > 5'd15));

  // No X/Z on outputs when inputs are known
  ap_no_x: assert property (@(A or B or Cin or Sum or Cout)
    !$isunknown({A,B,Cin}) |-> ##0 !$isunknown({Sum,Cout}));

  // Outputs don't change unless inputs do
  ap_stable: assert property (@(A or B or Cin or Sum or Cout)
    $stable({A,B,Cin}) |-> ##0 $stable({Sum,Cout}));

  // Simple identities
  ap_identity0: assert property (@(A or B or Cin)
    (!$isunknown({A,B,Cin}) && (B==4'd0) && (Cin==1'b0)) |-> ##0 (Sum==A && Cout==1'b0));
  ap_maxcase: assert property (@(A or B or Cin)
    (!$isunknown({A,B,Cin}) && (A==4'hF) && (B==4'hF) && (Cin==1'b1)) |-> ##0 (Sum==4'hF && Cout==1'b1));

  // Coverage: no-carry, carry, and boundary cases
  cp_no_carry:  cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) && (full_sum(A,B,Cin) <= 5'd15) && (Cout==1'b0));
  cp_carry:     cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) && (full_sum(A,B,Cin) >= 5'd16) && (Cout==1'b1));
  cp_edge_15:   cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) && (full_sum(A,B,Cin) == 5'd15) && (Cout==1'b0));
  cp_edge_16:   cover property (@(A or B or Cin) !$isunknown({A,B,Cin}) && (full_sum(A,B,Cin) == 5'd16) && (Cout==1'b1));

endmodule

// Bind into DUT
bind adder_with_overflow_detection adder_with_overflow_detection_sva sva_i (.*);