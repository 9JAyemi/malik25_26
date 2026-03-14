module shift_sel_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic [3:0] out
);
    // For sel==00, out is {in[3:2], 2'b00}.
    check_sel00_transform: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == {in[3:2], 2'b00})
    );

    // For sel==01, out is in & 4'b1100.
    check_sel01_transform: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == (in & 4'b1100))
    );

    // For sel==10, out is in | 4'b0011.
    check_sel10_transform: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == (in | 4'b0011))
    );

    // For sel==11, out is in ^ 4'b1010.
    check_sel11_transform: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == (in ^ 4'b1010))
    );

    // Bit 2 of out always passes through in[2] for all sel values.
    check_out2_passthrough: assert property (
        @(posedge clk) (out[2] == in[2])
    );

    // For sel==00, lower two bits are zero.
    check_sel00_lsb_zero: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out[1:0] == 2'b00)
    );

    // For sel==01, lower two bits are zero.
    check_sel01_lsb_zero: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out[1:0] == 2'b00)
    );

    // For sel==10, lower two bits are ones.
    check_sel10_lsb_one: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out[1:0] == 2'b11)
    );

    // MSB passes through when sel is not 2'b11.
    check_msb_passthrough_unless_xor: assert property (
        @(posedge clk) (sel != 2'b11) |-> (out[3] == in[3])
    );

    // For sel==11, bitwise behavior: invert bits 3 and 1, pass bits 2 and 0.
    check_sel11_bitwise_detail: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out[3] == ~in[3] && out[2] == in[2] && out[1] == ~in[1] && out[0] == in[0])
    );
endmodule