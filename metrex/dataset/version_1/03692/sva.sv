// SVA for ResetEither
module ResetEither_sva #(parameter bit REQUIRE_2STATE = 1) (
  input logic A_RST,
  input logic B_RST,
  input logic RST_OUT
);

  // Optional X/Z checking (2-state enforcement)
  a_no_x: assert property (@(A_RST or B_RST or RST_OUT)
                           (!REQUIRE_2STATE) or !$isunknown({A_RST,B_RST,RST_OUT}))
           else $error("ResetEither: X/Z detected on inputs/outputs");

  // Functional equivalence (combinational AND)
  a_func_and: assert property (@(A_RST or B_RST or RST_OUT)
                               RST_OUT === (A_RST & B_RST))
              else $error("ResetEither: RST_OUT != A_RST & B_RST");

  // Output edge correctness
  a_out_rise_inputs_high: assert property (@(posedge RST_OUT) (A_RST && B_RST))
                          else $error("ResetEither: RST_OUT rose without both inputs high");
  a_out_fall_input_low:   assert property (@(negedge RST_OUT) (!A_RST || !B_RST))
                          else $error("ResetEither: RST_OUT fell while both inputs high");

  // Input→Output immediate implications
  a_rise_A_when_B1: assert property (@(posedge A_RST) B_RST |-> RST_OUT)
                     else $error("ResetEither: RST_OUT not high when A rose and B was high");
  a_rise_B_when_A1: assert property (@(posedge B_RST) A_RST |-> RST_OUT)
                     else $error("ResetEither: RST_OUT not high when B rose and A was high");
  a_fall_A:         assert property (@(negedge A_RST) !RST_OUT)
                     else $error("ResetEither: RST_OUT not low when A fell");
  a_fall_B:         assert property (@(negedge B_RST) !RST_OUT)
                     else $error("ResetEither: RST_OUT not low when B fell");

  // Functional coverage
  c_combo_00: cover property (@(A_RST or B_RST) (!A_RST && !B_RST));
  c_combo_01: cover property (@(A_RST or B_RST) (!A_RST &&  B_RST));
  c_combo_10: cover property (@(A_RST or B_RST) ( A_RST && !B_RST));
  c_combo_11: cover property (@(A_RST or B_RST) ( A_RST &&  B_RST));

  c_out_rise: cover property (@(posedge RST_OUT) 1'b1);
  c_out_fall: cover property (@(negedge RST_OUT) 1'b1);

  c_rise_A_gate: cover property (@(posedge A_RST) B_RST && RST_OUT);
  c_rise_B_gate: cover property (@(posedge B_RST) A_RST && RST_OUT);
  c_fall_A_gate: cover property (@(negedge A_RST) !RST_OUT);
  c_fall_B_gate: cover property (@(negedge B_RST) !RST_OUT);

endmodule

// Bind SVA to DUT
bind ResetEither ResetEither_sva sva_i(.A_RST(A_RST), .B_RST(B_RST), .RST_OUT(RST_OUT));