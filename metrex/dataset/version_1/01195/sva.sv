// SVA for Round_Sgf_Dec
// Checks exact combinational spec and provides concise, targeted coverage.

module Round_Sgf_Dec_sva (
  input logic        clk,
  input logic [1:0]  Data_i,
  input logic [1:0]  Round_Type_i,
  input logic        Sign_Result_i,
  input logic        Round_Flag_o
);

  default clocking cb @(posedge clk); endclocking

  // Spec: Round_Flag_o == (Data!=0) AND ((RT==01 & S==1) OR (RT==10 & S==0))
  let flag_spec = (Data_i != 2'b00) &&
                  (((Round_Type_i == 2'b01) &&  Sign_Result_i) ||
                   ((Round_Type_i == 2'b10) && !Sign_Result_i));

  // Functional equivalence (single golden assertion)
  a_flag_spec: assert property (disable iff ($isunknown({Sign_Result_i,Round_Type_i,Data_i,Round_Flag_o}))
                                Round_Flag_o == flag_spec);

  // Minimal sanity negatives (redundant with main assert, but clearer debug)
  a_no_one_for_disallowed_rt: assert property (disable iff ($isunknown({Sign_Result_i,Round_Type_i,Data_i,Round_Flag_o}))
                                              !((Round_Type_i inside {2'b00,2'b11}) && Round_Flag_o));
  a_no_one_when_data_zero:    assert property (disable iff ($isunknown({Sign_Result_i,Round_Type_i,Data_i,Round_Flag_o}))
                                              !((Data_i == 2'b00) && Round_Flag_o));

  // Positive coverage: all six enumerated 5-bit cases
  c_pos_s1_rt01_d01: cover property ( Sign_Result_i && (Round_Type_i==2'b01) && (Data_i==2'b01) && Round_Flag_o);
  c_pos_s1_rt01_d10: cover property ( Sign_Result_i && (Round_Type_i==2'b01) && (Data_i==2'b10) && Round_Flag_o);
  c_pos_s1_rt01_d11: cover property ( Sign_Result_i && (Round_Type_i==2'b01) && (Data_i==2'b11) && Round_Flag_o);

  c_pos_s0_rt10_d01: cover property (!Sign_Result_i && (Round_Type_i==2'b10) && (Data_i==2'b01) && Round_Flag_o);
  c_pos_s0_rt10_d10: cover property (!Sign_Result_i && (Round_Type_i==2'b10) && (Data_i==2'b10) && Round_Flag_o);
  c_pos_s0_rt10_d11: cover property (!Sign_Result_i && (Round_Type_i==2'b10) && (Data_i==2'b11) && Round_Flag_o);

  // Negative coverage: representative defaults
  c_neg_data_zero:   cover property ((Data_i==2'b00) && !Round_Flag_o);
  c_neg_rt00:        cover property ((Round_Type_i==2'b00) && !Round_Flag_o);
  c_neg_rt11:        cover property ((Round_Type_i==2'b11) && !Round_Flag_o);
  c_neg_wrong_sign_rt01: cover property (!Sign_Result_i && (Round_Type_i==2'b01) && (Data_i inside {2'b01,2'b10,2'b11}) && !Round_Flag_o);
  c_neg_wrong_sign_rt10: cover property ( Sign_Result_i && (Round_Type_i==2'b10) && (Data_i inside {2'b01,2'b10,2'b11}) && !Round_Flag_o);

endmodule

// Bind into DUT
bind Round_Sgf_Dec Round_Sgf_Dec_sva sva_i (
  .clk(clk),
  .Data_i(Data_i),
  .Round_Type_i(Round_Type_i),
  .Sign_Result_i(Sign_Result_i),
  .Round_Flag_o(Round_Flag_o)
);