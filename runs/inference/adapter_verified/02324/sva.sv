module MIPS_Shifter_sva (
    input logic        clk,
    input logic [31:0] Data_in,
    input logic [4:0]  Count,
    input logic [1:0]  Sel,
    input logic [31:0] Data_out
);

// Count[0] selects between Data_in and {Data_in[30:0],1'b0}.
    check_count0_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (Data_out == (Sel[0] ? {Data_in[30:0], 1'b0} : Data_in))
    );

// Count[1] selects between Data_in and {Data_in[31:1],1'b0}.
    check_count1_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (Data_out == (Sel[1] ? {Data_in[31:1], 1'b0} : Data_in))
    );

// Count[2] selects between Data_in and {4{Data_in[31]}},Data_in[31:4]}.
    check_count2_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (Data_out == (Sel[1] ? {4{Data_in[31]}}, Data_in[31:4] : Data_in))
    );

// Count[3] selects between Data_in and {8{Data_in[31]}},Data_in[31:8]}.
    check_count3_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (Data_out == (Sel[1] ? {8{Data_in[31]}}, Data_in[31:8] : Data_in))
    );

// Count[4] selects between Data_in and {16{Data_in[31]}},Data_in[31:16]}.
    check_count4_select: assert property (
        @(posedge clk) disable iff (1'b0)
        (Data_out == (Sel[1] ? {16{Data_in[31]}}, Data_in[31:16] : Data_in))
    );

// When Sel==2'b00, output passes through unchanged.
    check_sel00_passthrough: assert property (
        @(posedge clk) disable iff (1'b0)
        (Sel == 2'b00) |-> (Data_out == Data_in)
    );

// When Sel==2'b01, output is zero-extended from Data_in[30:0].
    check_sel01_zero_extend: assert property (
        @(posedge clk) disable iff (1'b0)
        (Sel == 2'b01) |-> (Data_out == {Data_in[30:0], 1'b0})
    );

// When Sel==2'b10, output is zero-extended from Data_in[31:1].
    check_sel10_zero_extend: assert property (
        @(posedge clk) disable iff (1'b0)
        (Sel == 2'b10) |-> (Data_out == {Data_in[31:1], 1'b0})
    );

// When Sel==2'b11, output is zero-extended from Data_in[31].
    check_sel11_zero_extend: assert property (
        @(posedge clk) disable iff (1'b0)
        (Sel == 2'b11) |-> (Data_out == {31{Data_in[31]}}, 1'b0)
    );

endmodule
