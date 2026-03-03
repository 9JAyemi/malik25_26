// SVA bind checker for Round_Sgf_Dec
module Round_Sgf_Dec_sva (
  input logic [1:0] Data_i,
  input logic [1:0] Round_Type_i,
  input logic       Sign_Result_i,
  input logic       Round_Flag_o
);

  function automatic logic exp_flag(input logic [1:0] d,
                                    input logic [1:0] rt,
                                    input logic       s);
    return (d != 2'b00) && ((s && (rt==2'b01)) || (!s && (rt==2'b10)));
  endfunction

  // Combinational immediate checks and coverage
  always_comb begin
    bit inputs_known = !$isunknown({Data_i, Round_Type_i, Sign_Result_i});
    if (inputs_known) begin
      // No X/Z on output when inputs are known
      assert (!$isunknown(Round_Flag_o))
        else $error("Round_Flag_o X/Z with known inputs S=%0b RT=%0b D=%0b",
                    Sign_Result_i, Round_Type_i, Data_i);

      // Truth-table equivalence
      assert (Round_Flag_o === exp_flag(Data_i, Round_Type_i, Sign_Result_i))
        else $error("Round_Flag_o mismatch: got %0b exp %0b (S=%0b RT=%0b D=%0b)",
                    Round_Flag_o, exp_flag(Data_i,Round_Type_i,Sign_Result_i),
                    Sign_Result_i, Round_Type_i, Data_i);

      // Functional coverage
      cover (exp_flag(Data_i, Round_Type_i, Sign_Result_i)); // hit 1-cases
      cover (!exp_flag(Data_i, Round_Type_i, Sign_Result_i)); // hit 0-cases

      // Cover each explicit 1-case in the decoder
      cover ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10101);
      cover ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10110);
      cover ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10111);
      cover ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01001);
      cover ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01010);
      cover ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01011);

      // Cover representative default/0 paths
      cover (Data_i == 2'b00);
      cover ((Sign_Result_i && (Round_Type_i != 2'b01)) && (Data_i != 2'b00));
      cover ((!Sign_Result_i && (Round_Type_i != 2'b10)) && (Data_i != 2'b00));
    end
  end

endmodule

bind Round_Sgf_Dec Round_Sgf_Dec_sva u_Round_Sgf_Dec_sva (
  .Data_i        (Data_i),
  .Round_Type_i  (Round_Type_i),
  .Sign_Result_i (Sign_Result_i),
  .Round_Flag_o  (Round_Flag_o)
);