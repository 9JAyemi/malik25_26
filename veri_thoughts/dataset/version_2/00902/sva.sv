module SevenSegmentLED_sva (
    input logic clk,             // Sampling clock for SVA (DUT is purely combinational)
    input logic [3:0] i_data,
    input logic o_a,
    input logic o_b,
    input logic o_c,
    input logic o_d,
    input logic o_e,
    input logic o_f,
    input logic o_g
);
    // Analysis: No reset in RTL; no clock in RTL; logic is purely combinational 4-bit to 7-bit decode.

    // Outputs remain stable when inputs are stable (pure combinational function).
    check_stable_when_input_stable: assert property (
        @(posedge clk) disable iff (1'b0) $stable(i_data) |-> $stable({o_a,o_b,o_c,o_d,o_e,o_f,o_g})
    );

    // Decode mapping for 0x0 -> 7'b0000001
    check_decode_0: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h0) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0000001)
    );
    // Decode mapping for 0x1 -> 7'b1001111
    check_decode_1: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h1) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b1001111)
    );
    // Decode mapping for 0x2 -> 7'b0010010
    check_decode_2: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h2) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0010010)
    );
    // Decode mapping for 0x3 -> 7'b0000110
    check_decode_3: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h3) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0000110)
    );
    // Decode mapping for 0x4 -> 7'b1001100
    check_decode_4: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h4) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b1001100)
    );
    // Decode mapping for 0x5 -> 7'b0100100
    check_decode_5: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h5) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0100100)
    );
    // Decode mapping for 0x6 -> 7'b0100000
    check_decode_6: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h6) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0100000)
    );
    // Decode mapping for 0x7 -> 7'b0001111
    check_decode_7: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h7) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0001111)
    );
    // Decode mapping for 0x8 -> 7'b0000000
    check_decode_8: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h8) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0000000)
    );
    // Decode mapping for 0x9 -> 7'b0000100
    check_decode_9: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'h9) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0000100)
    );
    // Decode mapping for 0xa -> 7'b0001000
    check_decode_a: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'ha) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0001000)
    );
    // Decode mapping for 0xb -> 7'b1100000
    check_decode_b: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'hb) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b1100000)
    );
    // Decode mapping for 0xc -> 7'b0110001
    check_decode_c: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'hc) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0110001)
    );
    // Decode mapping for 0xd -> 7'b1000010
    check_decode_d: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'hd) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b1000010)
    );
    // Decode mapping for 0xe -> 7'b0110000
    check_decode_e: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'he) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0110000)
    );
    // Decode mapping for 0xf -> 7'b0111000
    check_decode_f: assert property (
        @(posedge clk) disable iff (1'b0) (i_data == 4'hf) |-> ({o_a,o_b,o_c,o_d,o_e,o_f,o_g} == 7'b0111000)
    );
endmodule