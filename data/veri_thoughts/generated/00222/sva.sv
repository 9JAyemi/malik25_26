module myNAND3_sva (
    input logic clk,
    input logic IN1,
    input logic IN2,
    input logic IN3,
    input logic QN
);

    // QN must equal the 3-input NAND of IN1, IN2, and IN3.
    check_nand3_function: assert property (
        @(posedge clk) QN == ~(IN1 & IN2 & IN3)
    );

    // When all inputs are high, QN must be low.
    check_all_high_drives_low: assert property (
        @(posedge clk) (IN1 && IN2 && IN3) |-> !QN
    );

    // If IN1 is low, QN must be high.
    check_in1_low_drives_high: assert property (
        @(posedge clk) !IN1 |-> QN
    );

    // If IN2 is low, QN must be high.
    check_in2_low_drives_high: assert property (
        @(posedge clk) !IN2 |-> QN
    );

    // If IN3 is low, QN must be high.
    check_in3_low_drives_high: assert property (
        @(posedge clk) !IN3 |-> QN
    );

    // A low QN is only possible when all three inputs are high.
    check_low_output_requires_all_high: assert property (
        @(posedge clk) !QN |-> (IN1 && IN2 && IN3)
    );

endmodule