// SVA for logic_gate
// Bind-friendly, concise, and covers functionality, reset, unknowns, and both select paths.

module logic_gate_sva (
  input A1,
  input [1:0] select,
  input A2,
  input A3,
  input B1,
  input C1,
  input reset,
  input X,
  input valid
);

  // Trigger on any input/reset change to align with combinational DUT
  default clocking cb @ (A1 or select or A2 or A3 or B1 or C1 or reset); endclocking

  // Expected function
  let exp = (select==2'b00) ? (A1 && A2 && A3) : (A1 && B1 && C1);

  // Reset drives zeros (and not X/Z), sample after combinational update
  a_reset_zeros: assert property (reset |-> ##0 (X===1'b0 && valid===1'b0));

  // Outputs are known and match the function when inputs are known and not in reset
  a_known_io_match: assert property (
    (!reset && !$isunknown({A1,A2,A3,B1,C1,select})) |-> ##0
      (!$isunknown({X,valid}) && X==exp && valid==exp)
  );

  // valid always equals X (catch accidental divergence)
  a_valid_eq_x: assert property (1'b1 |-> ##0 (valid===X));

  // Functional coverage: both select paths, true/false outcomes, and reset behavior
  c_00_true:   cover property ((!reset && select==2'b00 &&  A1 && A2 && A3) ##0 ( X &&  valid));
  c_00_false:  cover property ((!reset && select==2'b00 && !(A1 && A2 && A3)) ##0 (!X && !valid));
  c_ne00_true: cover property ((!reset && select!=2'b00 &&  A1 && B1 && C1) ##0 ( X &&  valid));
  c_ne00_false:cover property ((!reset && select!=2'b00 && !(A1 && B1 && C1)) ##0 (!X && !valid));
  c_reset:     cover property (reset ##0 (X==1'b0 && valid==1'b0));

endmodule

// Example bind (instantiate once per DUT instance)
// bind logic_gate logic_gate_sva sva (.*);