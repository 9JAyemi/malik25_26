module Round_Sgf_Dec_sva(
    input logic [1:0] Data_i,
    input logic [1:0] Round_Type_i,
    input logic Sign_Result_i,
    input logic Round_Flag_o
);

    // Round_Flag_o matches the full decode truth table.
    check_round_flag_truth_table: assert property (
        @($global_clock)
        Round_Flag_o == (
            (((Sign_Result_i == 1'b1) && (Round_Type_i == 2'b01)) ||
             ((Sign_Result_i == 1'b0) && (Round_Type_i == 2'b10))) &&
            (Data_i != 2'b00)
        )
    );

    // Zero data never asserts the round flag.
    check_zero_data_clears_flag: assert property (
        @($global_clock)
        (Data_i == 2'b00) |-> (Round_Flag_o == 1'b0)
    );

    // Sign_Result_i=1 with Round_Type_i=01 and nonzero data asserts the flag.
    check_sign1_round01_nonzero_sets_flag: assert property (
        @($global_clock)
        ((Sign_Result_i == 1'b1) && (Round_Type_i == 2'b01) && (Data_i != 2'b00)) |-> (Round_Flag_o == 1'b1)
    );

    // Sign_Result_i=0 with Round_Type_i=10 and nonzero data asserts the flag.
    check_sign0_round10_nonzero_sets_flag: assert property (
        @($global_clock)
        ((Sign_Result_i == 1'b0) && (Round_Type_i == 2'b10) && (Data_i != 2'b00)) |-> (Round_Flag_o == 1'b1)
    );

    // A high round flag requires nonzero data.
    check_flag_requires_nonzero_data: assert property (
        @($global_clock)
        (Round_Flag_o == 1'b1) |-> (Data_i != 2'b00)
    );

    // When Sign_Result_i is 1, a high flag only occurs in round type 01.
    check_sign1_flag_only_in_round01: assert property (
        @($global_clock)
        ((Round_Flag_o == 1'b1) && (Sign_Result_i == 1'b1)) |-> (Round_Type_i == 2'b01)
    );

    // When Sign_Result_i is 0, a high flag only occurs in round type 10.
    check_sign0_flag_only_in_round10: assert property (
        @($global_clock)
        ((Round_Flag_o == 1'b1) && (Sign_Result_i == 1'b0)) |-> (Round_Type_i == 2'b10)
    );

    // Round types 00 and 11 never assert the round flag.
    check_unused_round_types_clear_flag: assert property (
        @($global_clock)
        ((Round_Type_i == 2'b00) || (Round_Type_i == 2'b11)) |-> (Round_Flag_o == 1'b0)
    );

    // Sign_Result_i=1 with round type 10 never asserts the flag.
    check_sign1_round10_clears_flag: assert property (
        @($global_clock)
        ((Sign_Result_i == 1'b1) && (Round_Type_i == 2'b10)) |-> (Round_Flag_o == 1'b0)
    );

    // Sign_Result_i=0 with round type 01 never asserts the flag.
    check_sign0_round01_clears_flag: assert property (
        @($global_clock)
        ((Sign_Result_i == 1'b0) && (Round_Type_i == 2'b01)) |-> (Round_Flag_o == 1'b0)
    );

endmodule