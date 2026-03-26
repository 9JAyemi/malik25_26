module four_input_module_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2
);

    // X must implement a NAND of A1 and B1.
    check_nand_function: assert property (
        @(posedge clk) X === ~(A1 & B1)
    );

    // X must be low when both inputs are high.
    check_both_high_drive_low: assert property (
        @(posedge clk) (A1 === 1'b1 && B1 === 1'b1) |-> (X === 1'b0)
    );

    // X must be high when both inputs are low.
    check_both_low_drive_high: assert property (
        @(posedge clk) (A1 === 1'b0 && B1 === 1'b0) |-> (X === 1'b1)
    );

    // X must be high when A1 is low and B1 is high.
    check_a1_low_b1_high_drive_high: assert property (
        @(posedge clk) (A1 === 1'b0 && B1 === 1'b1) |-> (X === 1'b1)
    );

    // X must be high when A1 is high and B1 is low.
    check_a1_high_b1_low_drive_high: assert property (
        @(posedge clk) (A1 === 1'b1 && B1 === 1'b0) |-> (X === 1'b1)
    );

endmodule