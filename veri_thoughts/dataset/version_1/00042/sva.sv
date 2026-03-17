module priority_encoder_sva (
    input logic [7:0] in,
    input logic [1:0] pos,
    input logic [3:0] out_sel,
    input logic clk
);

    // Bit 7 has highest priority and drives the next registered outputs.
    check_bit7_priority: assert property (
        @(posedge clk)
        in[7] |=> (pos == 2'b11 && out_sel == 4'b0001)
    );

    // Bit 6 is selected when bit 7 is low.
    check_bit6_priority: assert property (
        @(posedge clk)
        ((in[7] == 1'b0) && (in[6] == 1'b1)) |=> (pos == 2'b10 && out_sel == 4'b0010)
    );

    // Bit 5 is selected when bits 7 and 6 are low.
    check_bit5_priority: assert property (
        @(posedge clk)
        ((in[7:6] == 2'b00) && (in[5] == 1'b1)) |=> (pos == 2'b00 && out_sel == 4'b0100)
    );

    // Bit 4 is selected when bits 7 through 5 are low.
    check_bit4_priority: assert property (
        @(posedge clk)
        ((in[7:5] == 3'b000) && (in[4] == 1'b1)) |=> (pos == 2'b11 && out_sel == 4'b1000)
    );

    // Bit 3 is selected when bits 7 through 4 are low.
    check_bit3_priority: assert property (
        @(posedge clk)
        ((in[7:4] == 4'b0000) && (in[3] == 1'b1)) |=> (pos == 2'b10 && out_sel == 4'b0000)
    );

    // Bit 2 is selected when bits 7 through 3 are low.
    check_bit2_priority: assert property (
        @(posedge clk)
        ((in[7:3] == 5'b00000) && (in[2] == 1'b1)) |=> (pos == 2'b01 && out_sel == 4'b0000)
    );

    // Bit 1 is selected when bits 7 through 2 are low.
    check_bit1_priority: assert property (
        @(posedge clk)
        ((in[7:2] == 6'b000000) && (in[1] == 1'b1)) |=> (pos == 2'b00 && out_sel == 4'b0000)
    );

    // When bits 7 through 1 are clear, bit 0 is ignored and outputs go to zero.
    check_no_selected_bit_or_bit0_only: assert property (
        @(posedge clk)
        (in[7:1] == 7'b0000000) |=> (pos == 2'b00 && out_sel == 4'b0000)
    );

endmodule