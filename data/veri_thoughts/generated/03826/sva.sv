module Round_Sgf_Dec_assertions (
    input logic clk,
    input logic [1:0] Data_i,
    input logic [1:0] Round_Type_i,
    input logic Sign_Result_i,
    input logic Round_Flag_o
);

    // Positive-sign decode cases drive Round_Flag_o high.
    check_round_flag_positive_sign_cases: assert property (
        @(posedge clk)
        (
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10101) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10110) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10111)
        ) |-> (Round_Flag_o == 1'b1)
    );

    // Negative-sign decode cases drive Round_Flag_o high.
    check_round_flag_negative_sign_cases: assert property (
        @(posedge clk)
        (
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01001) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01010) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01011)
        ) |-> (Round_Flag_o == 1'b1)
    );

    // All unlisted decode cases drive Round_Flag_o low.
    check_round_flag_default_zero: assert property (
        @(posedge clk)
        (
            ({Sign_Result_i, Round_Type_i, Data_i} != 5'b10101) &&
            ({Sign_Result_i, Round_Type_i, Data_i} != 5'b10110) &&
            ({Sign_Result_i, Round_Type_i, Data_i} != 5'b10111) &&
            ({Sign_Result_i, Round_Type_i, Data_i} != 5'b01001) &&
            ({Sign_Result_i, Round_Type_i, Data_i} != 5'b01010) &&
            ({Sign_Result_i, Round_Type_i, Data_i} != 5'b01011)
        ) |-> (Round_Flag_o == 1'b0)
    );

    // A high Round_Flag_o only occurs on one of the listed cases.
    check_round_flag_high_only_on_listed_cases: assert property (
        @(posedge clk)
        (Round_Flag_o == 1'b1) |-> (
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10101) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10110) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10111) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01001) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01010) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01011)
        )
    );

    // Round_Flag_o matches the complete combinational decode.
    check_round_flag_complete_truth_table: assert property (
        @(posedge clk)
        Round_Flag_o == (
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10101) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10110) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b10111) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01001) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01010) ||
            ({Sign_Result_i, Round_Type_i, Data_i} == 5'b01011)
        )
    );

endmodule