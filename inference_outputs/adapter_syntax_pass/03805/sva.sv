module Test6_sva (
    input logic clk,
    input logic OE,
    input logic [3:0] Z10
);

    // When OE is high, Z10[1:0] must be 10.
    check_oe_high_lower_pair: assert property (
        @(posedge clk) OE |-> (Z10[1:0] == 2'b10)
    );

    // When OE is low, Z10[1:0] must be 01.
    check_oe_low_lower_pair: assert property (
        @(posedge clk) !OE |-> (Z10[1:0] == 2'b01)
    );

    // When OE is high, Z10[3:2] must be 01.
    check_oe_high_upper_pair: assert property (
        @(posedge clk) OE |-> (Z10[3:2] == 2'b01)
    );

    // When OE is low, Z10[3:2] must be 10.
    check_oe_low_upper_pair: assert property (
        @(posedge clk) !OE |-> (Z10[3:2] == 2'b10)
    );

    // The lower pair must always be the inverse of the upper pair.
    check_lower_pair_inverts_upper_pair: assert property (
        @(posedge clk) (Z10[1:0] == ~Z10[3:2])
    );

endmodule