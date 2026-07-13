module Test6_assertions (
    input logic clk,
    input logic OE,
    input logic [3:0] Z10
);

    // Lower pair follows instance a.
    check_lower_pair_drive: assert property (
        @(posedge clk) {Z10[1], Z10[0]} == (OE ? 2'b10 : 2'b01)
    );

    // Upper pair follows instance b with inverted OE.
    check_upper_pair_drive: assert property (
        @(posedge clk) {Z10[3], Z10[2]} == (OE ? 2'b01 : 2'b10)
    );

    // Middle bits both track OE.
    check_middle_bits_follow_oe: assert property (
        @(posedge clk) {Z10[2], Z10[1]} == {2{OE}}
    );

    // Outer bits both track inverted OE.
    check_outer_bits_follow_inverted_oe: assert property (
        @(posedge clk) {Z10[3], Z10[0]} == {2{~OE}}
    );

    // OE high produces the full driven bus pattern.
    check_bus_pattern_when_oe_high: assert property (
        @(posedge clk) OE |-> (Z10 == 4'b0110)
    );

    // OE low produces the full driven bus pattern.
    check_bus_pattern_when_oe_low: assert property (
        @(posedge clk) !OE |-> (Z10 == 4'b1001)
    );

endmodule