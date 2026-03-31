module Test6_sva (
    input logic clk,
    input logic OE,
    input logic [3:0] Z10
);

// When OE is high, Z10[1:0] must be 10.
    check_oe_high_swaps_low_pair: assert property (
        @(posedge clk) OE |-> (Z10[1:0] == 2'b10)
    );

// When OE is low, Z10[1:0] must be 01.
    check_oe_low_keeps_low_pair: assert property (
        @(posedge clk) !OE |-> (Z10[1:0] == 2'b01)
    );

// When OE is high, Z10[3:2] must be 10.
    check_oe_high_swaps_high_pair: assert property (
        @(posedge clk) OE |-> (Z10[3:2] == 2'b10)
    );

// When OE is low, Z10[3:2] must be 01.
    check_oe_low_keeps_high_pair: assert property (
        @(posedge clk) !OE |-> (Z10[3:2] == 2'b01)
    );

// The full 4-bit output must always be 1001.
    check_full_output_pattern: assert property (
        @(posedge clk) Z10 == 4'b1001
    );

endmodule
