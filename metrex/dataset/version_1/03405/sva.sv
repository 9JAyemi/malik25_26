// SVA for sky130_fd_sc_hd__o221ai
// Function: Y = ~((A1|A2) & (B1|B2) & C1)

module sky130_fd_sc_hd__o221ai_sva (
  input logic A1, A2, B1, B2, C1, Y
);

  default clocking cb @(*); endclocking

  function automatic logic fY (input logic A1, A2, B1, B2, C1);
    return ~((A1|A2) & (B1|B2) & C1);
  endfunction

  // 4-state functional equivalence (covers X/Z propagation consistency)
  a_func_4state: assert property (Y === fY(A1,A2,B1,B2,C1));

  // When inputs are known 0/1, output must be known and correct
  a_func_known:  assert property (!$isunknown({A1,A2,B1,B2,C1}) |-> (! $isunknown(Y) && Y === fY(A1,A2,B1,B2,C1)));

  // Dominating cases (deterministic even with Xs on non-controlling inputs)
  a_dom_c1_0:    assert property ((C1 === 1'b0)                                   |-> (Y === 1'b1));
  a_dom_a_zero:  assert property ((A1 === 1'b0 && A2 === 1'b0)                    |-> (Y === 1'b1));
  a_dom_b_zero:  assert property ((B1 === 1'b0 && B2 === 1'b0)                    |-> (Y === 1'b1));
  a_force_zero:  assert property ((C1 === 1'b1) && ((A1===1'b1)||(A2===1'b1)) &&
                                  ((B1===1'b1)||(B2===1'b1))                      |-> (Y === 1'b0));

  // Coverage: all input combinations and their resulting Y
  covergroup cg_inputs @(A1 or A2 or B1 or B2 or C1 or Y);
    cp_inputs: coverpoint {A1,A2,B1,B2,C1} { bins all[] = {[0:31]}; }
    cp_y:      coverpoint Y { bins zero = {1'b0}; bins one = {1'b1}; bins xz = default; }
    cx:        cross cp_inputs, cp_y;
  endgroup
  cg_inputs cg = new;

  // Key scenario covers
  c_y_one_c1_zero: cover property (C1===1'b0 && Y===1'b1);
  c_y_one_a_zero:  cover property (A1===1'b0 && A2===1'b0 && Y===1'b1);
  c_y_one_b_zero:  cover property (B1===1'b0 && B2===1'b0 && Y===1'b1);
  c_y_zero:        cover property (C1===1'b1 && (A1||A2) && (B1||B2) && Y===1'b0);

endmodule

bind sky130_fd_sc_hd__o221ai sky130_fd_sc_hd__o221ai_sva u_o221ai_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .Y(Y)
);