module Round_Sgf_Dec_sva (
    input logic [1:0] Data_i,
    input logic [1:0] Round_Type_i,
    input logic Sign_Result_i,
    input logic Round_Flag_o
);

    // Round_Flag_o matches the six explicit case items in the RTL.
    check_round_flag_exact_decode: assert property (
        @($global_clock)
        Round_Flag_o === (
            ({Sign_Result_i, Round_Type_i, Data_i} === 5'b10101) ||
            ({Sign_Result_i, Round_Type_i, Data_i} === 5'b10110) ||
            ({Sign_Result_i, Round_Type_i, Data_i} === 5'b10111) ||
            ({Sign_Result_i, Round_Type_i, Data_i} === 5'b01001) ||
            ({Sign_Result_i, Round_Type_i, Data_i} === 5'b01010) ||
            ({Sign_Result_i, Round_Type_i, Data_i} === 5'b01011)
        )
    );

    // Sign 1, round type 01, and nonzero data set the flag.
    check_type01_positive_nonzero_sets_flag: assert property (
        @($global_clock)
        ((Sign_Result_i === 1'b1) &&
         (Round_Type_i === 2'b01) &&
         ((Data_i === 2'b01) || (Data_i === 2'b10) || (Data_i === 2'b11)))
        |-> (Round_Flag_o === 1'b1)
    );

    // Sign 0, round type 10, and nonzero data set the flag.
    check_type10_negative_nonzero_sets_flag: assert property (
        @($global_clock)
        ((Sign_Result_i === 1'b0) &&
         (Round_Type_i === 2'b10) &&
         ((Data_i === 2'b01) || (Data_i === 2'b10) || (Data_i === 2'b11)))
        |-> (Round_Flag_o === 1'b1)
    );

    // Zero data always clears the flag.
    check_zero_data_clears_flag: assert property (
        @($global_clock)
        (Data_i === 2'b00) |-> (Round_Flag_o === 1'b0)
    );

    // Round type 00 always clears the flag.
    check_round_type00_clears_flag: assert property (
        @($global_clock)
        (Round_Type_i === 2'b00) |-> (Round_Flag_o === 1'b0)
    );

    // Round type 11 always clears the flag.
    check_round_type11_clears_flag: assert property (
        @($global_clock)
        (Round_Type_i === 2'b11) |-> (Round_Flag_o === 1'b0)
    );

    // Round type 01 with sign 0 never sets the flag.
    check_type01_negative_clears_flag: assert property (
        @($global_clock)
        ((Sign_Result_i === 1'b0) && (Round_Type_i === 2'b01)) |-> (Round_Flag_o === 1'b0)
    );

    // Round type 10 with sign 1 never sets the flag.
    check_type10_positive_clears_flag: assert property (
        @($global_clock)
        ((Sign_Result_i === 1'b1) && (Round_Type_i === 2'b10)) |-> (Round_Flag_o === 1'b0)
    );

    // A high flag requires nonzero data.
    check_flag_high_requires_nonzero_data: assert property (
        @($global_clock)
        (Round_Flag_o === 1'b1) |-> ((Data_i === 2'b01) || (Data_i === 2'b10) || (Data_i === 2'b11))
    );

    // A high flag requires one of the two valid sign/type pairings.
    check_flag_high_requires_supported_sign_type: assert property (
        @($global_clock)
        (Round_Flag_o === 1'b1) |-> (
            ((Sign_Result_i === 1'b1) && (Round_Type_i === 2'b01)) ||
            ((Sign_Result_i === 1'b0) && (Round_Type_i === 2'b10))
        )
    );

endmodule