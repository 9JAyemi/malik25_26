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

    // out1 matches the implemented combinational function.
    check_out1_function: assert property (
        @(posedge clk)
        out1 == ((in1 & in2) & (in3 & in4) & (in5 & in6) & (in7 & in8) & in9)
    );

    // A low in9 forces out1 low.
    check_in9_low_forces_out1_low: assert property (
        @(posedge clk)
        !in9 |-> !out1
    );

    // All four 2-input AND terms high force out1 high.
    check_all_terms_high_force_out1_high: assert property (
        @(posedge clk)
        ((in1 & in2) & (in3 & in4) & (in5 & in6) & (in7 & in8)) |-> out1
    );

    // A low in1 forces out1 low.
    check_in1_low_forces_out1_low: assert property (
        @(posedge clk)
        !in1 |-> !out1
    );

    // A low in2 forces out1 low.
    check_in2_low_forces_out1_low: assert property (
        @(posedge clk)
        !in2 |-> !out1
    );

    // A low in3 forces out1 low.
    check_in3_low_forces_out1_low: assert property (
        @(posedge clk)
        !in3 |-> !out1
    );

    // A low in4 forces out1 low.
    check_in4_low_forces_out1_low: assert property (
        @(posedge clk)
        !in4 |-> !out1
    );

    // A low in5 forces out1 low.
    check_in5_low_forces_out1_low: assert property (
        @(posedge clk)
        !in5 |-> !out1
    );

    // A low in6 forces out1 low.
    check_in6_low_forces_out1_low: assert property (
        @(posedge clk)
        !in6 |-> !out1
    );

    // A low in7 forces out1 low.
    check_in7_low_forces_out1_low: assert property (
        @(posedge clk)
        !in7 |-> !out1
    );

    // A low in8 forces out1 low.
    check_in8_low_forces_out1_low: assert property (
        @(posedge clk)
        !in8 |-> !out1
    );

endmodule