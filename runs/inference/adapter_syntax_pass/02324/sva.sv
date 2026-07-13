module MIPS_Shifter_sva (
    input logic        clk,
    input logic [31:0] Data_in,
    input logic [4:0]  Count,
    input logic [1:0]  Sel,
    input logic [31:0] Data_out
);

    // Count[0] selects between Data_in and the zero-extended upper 30 bits.
    check_count0_select: assert property (
        @(posedge clk)
        (Data_out == (Count[0] ? {32'b0, Data_in[30:0]} : Data_in))
    );

    // Count[1] selects between the zero-extended upper 29 bits and the upper 31 bits.
    check_count1_select: assert property (
        @(posedge clk)
        (Data_out == (Count[1] ? {32'b0, Data_in[29:0]} : {Data_in[31:0]}))
    );

    // Count[2] selects between the zero-extended upper 27 bits and the upper 31 bits.
    check_count2_select: assert property (
        @(posedge clk)
        (Data_out == (Count[2] ? {32'b0, Data_in[27:0]} : {Data_in[31:0]}))
    );

    // Count[3] selects between the zero-extended upper 23 bits and the upper 31 bits.
    check_count3_select: assert property (
        @(posedge clk)
        (Data_out == (Count[3] ? {32'b0, Data_in[23:0]} : {Data_in[31:0]}))
    );

    // Count[4] selects between the zero-extended upper 15 bits and the upper 31 bits.
    check_count4_select: assert property (
        @(posedge clk)
        (Data_out == (Count[4] ? {32'b0, Data_in[15:0]} : {Data_in[31:0]}))
    );

    // Zero count leaves the output unchanged.
    check_zero_count_passthrough: assert property (
        @(posedge clk)
        (Count == 5'd0) |-> (Data_out == Data_in)
    );

    // All ones on Count selects the zero-extended upper 15 bits.
    check_all_ones_count_selects_upper_15: assert property (
        @(posedge clk)
        (Count == 5'h1F) |-> (Data_out == {32'b0, Data_in[15:0]})
    );

    // With Count[4] high, the output is always zero-extended.
    check_count4_high_zero_extends_output: assert property (
        @(posedge clk)
        Count[4] |-> (Data_out[31:16] == 16'b0)
    );

    // With Count[3] high, the output is always zero-extended.
    check_count3_high_zero_extends_output: assert property (
        @(posedge clk)
        Count[3] |-> (Data_out[31:8] == 24'b0)
    );

    // With Count[2] high, the output is always zero-extended.
    check_count2_high_zero_extends_output: assert property (
        @(posedge clk)
        Count[2] |-> (Data_out[31:4] == 28'b0)
    );

    // With Count[1] high, the output is always zero-extended.
    check_count1_high_zero_extends_output: assert property (
        @(posedge clk)
        Count[1] |-> (Data_out[31:2] == 30'b0)
    );

    // With Count[0] high, the output is always zero-extended.
    check_count0_high_zero_extends_output: assert property (
        @(posedge clk)
        Count[0] |-> (Data_out[31:1] == 31'b0)
    );

endmodule