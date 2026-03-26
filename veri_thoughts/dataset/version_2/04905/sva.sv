module four_to_sixteen_decoder_sva (
    input logic clk,
    input logic [1:0] sel,
    input logic [15:0] out
);

    // Combinational decoder sampled on an external clock; no reset exists in the RTL.

    // sel=00 drives bit 0 high.
    check_sel_00_decodes_bit0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == 16'b0000000000000001)
    );

    // sel=01 drives bit 1 high.
    check_sel_01_decodes_bit1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == 16'b0000000000000010)
    );

    // sel=10 drives bit 2 high.
    check_sel_10_decodes_bit2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == 16'b0000000000000100)
    );

    // sel=11 drives bit 3 high.
    check_sel_11_decodes_bit3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == 16'b0000000000001000)
    );

    // The full output matches a 1 shifted by sel.
    check_full_output_matches_decode: assert property (
        @(posedge clk) out == (16'h0001 << sel)
    );

    // Upper output bits are always zero.
    check_upper_bits_zero: assert property (
        @(posedge clk) out[15:4] == 12'b0
    );

endmodule