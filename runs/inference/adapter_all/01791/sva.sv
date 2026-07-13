module power_good_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic in8,
    input logic in9,
    input logic out1
);

    // out1 matches the nested AND expression implemented in the RTL.
    check_out1_matches_nested_and: assert property (
        @(posedge clk)
        out1 == ((in1 & in2) & (in3 & in4) & (in5 & in6) & (in7 & in8) & (in9 & (in1 & in2) & (in3 & in4) & (in5 & in6) & (in7 & in8)))
    );

    // out1 reduces to the simple AND of all nine inputs.
    check_out1_reduces_to_simple_and: assert property (
        @(posedge clk)
        out1 == (in1 & in2 & in3 & in4 & in5 & in6 & in7 & in8 & in9)
    );

    // All nine high inputs must drive out1 high.
    check_all_inputs_high_drive_out1_high: assert property (
        @(posedge clk)
        (in1 & in2 & in3 & in4 & in5 & in6 & in7 & in8 & in9) |-> out1
    );

    // A low in1 must force out1 low.
    check_in1_low_forces_out1_low: assert property (
        @(posedge clk)
        !in1 |-> !out1
    );

    // A low in2 must force out1 low.
    check_in2_low_forces_out1_low: assert property (
        @(posedge clk)
        !in2 |-> !out1
    );

    // A low in3 must force out1 low.
    check_in3_low_forces_out1_low: assert property (
        @(posedge clk)
        !in3 |-> !out1
    );

    // A low in4 must force out1 low.
    check_in4_low_forces_out1_low: assert property (
        @(posedge clk)
        !in4 |-> !out1
    );

    // A low in5 must force out1 low.
    check_in5_low_forces_out1_low: assert property (
        @(posedge clk)
        !in5 |-> !out1
    );

    // A low in6 must force out1 low.
    check_in6_low_forces_out1_low: assert property (
        @(posedge clk)
        !in6 |-> !out1
    );

    // A low in7 must force out1 low.
    check_in7_low_forces_out1_low: assert property (
        @(posedge clk)
        !in7 |-> !out1
    );

    // A low in8 must force out1 low.
    check_in8_low_forces_out1_low: assert property (
        @(posedge clk)
        !in8 |-> !out1
    );

    // A low in9 must force out1 low.
    check_in9_low_forces_out1_low: assert property (
        @(posedge clk)
        !in9 |-> !out1
    );

endmodule