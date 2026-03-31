module MIPS_Shifter_sva (
    input logic        clk,
    input logic [31:0] Data_in,
    input logic [4:0]  Count,
    input logic [1:0]  Sel,
    input logic [31:0] Data_out
);

    // RTL is combinational; clk is only used to sample assertions.

    // Count[0] selects between Data_in and Data_in shifted left by 1.
    check_count0_selects_left_shift: assert property (
        @(posedge clk)
        Data_out == (Count[0] ? {Data_in[30:0], 1'b0} : {Data_in[31:1], Data_in[0]})
    );

    // Count[1] selects between the Count[0] result and the Count[0] result shifted left by 1.
    check_count1_selects_left_shift: assert property (
        @(posedge clk)
        Data_out == (Count[1] ? {Data_out[29:0], 2'b00} : {Data_out[30:0], Data_out[0]})
    );

    // Count[2] selects between the Count[1] result and the Count[1] result shifted left by 1.
    check_count2_selects_left_shift: assert property (
        @(posedge clk)
        Data_out == (Count[2] ? {Data_out[27:0], 4'b0000} : {Data_out[29:0], Data_out[0]})
    );

    // Count[3] selects between the Count[2] result and the Count[2] result shifted left by 1.
    check_count3_selects_left_shift: assert property (
        @(posedge clk)
        Data_out == (Count[3] ? {Data_out[23:0], 8'b00000000} : {Data_out[29:0], Data_out[0]})
    );

    // Count[4] selects between the Count[3] result and the Count[3] result shifted left by 1.
    check_count4_selects_left_shift: assert property (
        @(posedge clk)
        Data_out == (Count[4] ? {Data_out[15:0], 16'b0000000000000000} : {Data_out[29:0], Data_out[0]})
    );

    // With Count[4] low, the final result is the Count[3] result shifted left by 1.
    check_final_shift_when_count4_low: assert property (
        @(posedge clk)
        !Count[4] |-> (Data_out == {Data_out[29:0], Data_out[0]})
    );

    // With Count[4] high, the final result is the Count[3] result shifted left by 2.
    check_final_shift_when_count4_high: assert property (
        @(posedge clk)
        Count[4] |-> (Data_out == {Data_out[27:0], 2'b00})
    );

    // With Count[3] low, the Count[2] result is either zero-extended or sign-extended by 1 bit.
    check_count2_selects_sign_or_zero_extend: assert property (
        @(posedge clk)
        !Count[3] |-> (Data_out == (Count[2] ? {Data_out[27:0], 4'b0000} : {Data_out[29:0], Data_out[0]}))
    );

    // With Count[3] high, the Count[2] result is zero-extended by 2 bits.
    check_count2_selects_zero_extend: assert property (
        @(posedge clk)
        Count[3] |-> (Data_out == {Data_out[27:0], 4'b0000})
    );

    // With Count[2] low, the Count[1] result is either zero-extended or sign-extended by 1 bit.
    check_count1_selects_sign_or_zero_extend: assert property (
        @(posedge clk)
        !Count[2] |-> (Data_out == (Count[1] ? {Data_out[29:0], 2'b00} : {Data_out[29:0], Data_out[0]}))
    );

    // With Count[2] high, the Count[1] result is zero-extended by 2 bits.
    check_count1_selects_zero_extend: assert property (
        @(posedge clk)
        Count[2] |-> (Data_out == {Data_out[29:0], 2'b00})
    );

    // With Count[1] low, the Count[0] result is either zero-extended or sign-extended by 1 bit.
    check_count0_selects_sign_or_zero_extend: assert property (
        @(posedge clk)
        !Count[1] |-> (Data_out == (Count[0] ? {Data_out[30:0], 1'b0} : {Data_out[31:1], Data_out[0]}))
    );

    // With Count[1] high, the Count[0] result is zero-extended by 2 bits.
    check_count0_selects_zero_extend: assert property (
        @(posedge clk)
        Count[1] |-> (Data_out == {Data_out[30:0], 1'b0})
    );

endmodule