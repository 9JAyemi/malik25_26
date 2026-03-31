```systemverilog
module hexledx_sva (
    input wire [3:0] value,
    input wire blank,
    input wire minus,
    input wire clk,
    input wire rst_n
);
    // Sequential logic with clocked assertions

    // At reset, s7 should be 0
    reset_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (s7 == 7'b0000000)
    );

    // When blank is high, s7 should be 0
    blank_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (blank |-> s7 == 7'b0000000)
    );

    // When minus is high, s7 should be 0x40 (1000000)
    minus_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (minus |-> s7 == 7'b1000000)
    );

    // When value is 0, s7 should be 0x3F (0111111)
    value_0_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h0 |-> s7 == 7'b0111111)
    );

    // When value is 1, s7 should be 0x06 (0000110)
    value_1_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h1 |-> s7 == 7'b0000110)
    );

    // When value is 2, s7 should be 0x5B (1011011)
    value_2_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h2 |-> s7 == 7'b1011011)
    );

    // When value is 3, s7 should be 0x4F (1001111)
    value_3_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h3 |-> s7 == 7'b1001111)
    );

    // When value is 4, s7 should be 0x66 (1100110)
    value_4_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h4 |-> s7 == 7'b1100110)
    );

    // When value is 5, s7 should be 0x6D (1101101)
    value_5_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h5 |-> s7 == 7'b1101101)
    );

    // When value is 6, s7 should be 0x7D (1111101)
    value_6_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h6 |-> s7 == 7'b1111101)
    );

    // When value is 7, s7 should be 0x07 (0000111)
    value_7_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h7 |-> s7 == 7'b0000111)
    );

    // When value is 8, s7 should be 0x7F (1111111)
    value_8_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h8 |-> s7 == 7'b1111111)
    );

    // When value is 9, s7 should be 0x6F (1101111)
    value_9_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'h9 |-> s7 == 7'b1101111)
    );

    // When value is A, s7 should be 0x77 (1110111)
    value_A_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'hA |-> s7 == 7'b1110111)
    );

    // When value is B, s7 should be 0x7C (1111100)
    value_B_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'hB |-> s7 == 7'b1111100)
    );

    // When value is C, s7 should be 0x39 (0111001)
    value_C_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'hC |-> s7 == 7'b0111001)
    );

    // When value is D, s7 should be 0x5E (1011110)
    value_D_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'hD |-> s7 == 7'b1011110)
    );

    // When value is E, s7 should be 0x79 (1111001)
    value_E_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'hE |-> s7 == 7'b1111001)
    );

    // When value is F, s7 should be 0x71 (1110001)
    value_F_s7: assert property (
        @(posedge clk) disable iff (!rst_n) (value == 4'hF |-> s7 == 7'b1110001)
    );
endmodule
```