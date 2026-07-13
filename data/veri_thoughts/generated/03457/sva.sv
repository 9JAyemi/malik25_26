module and_gate_with_inverter_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1
);

    // C1 high forces the output low.
    check_c1_forces_output_low: assert property (
        @(posedge clk)
        (C1 === 1'b1) |-> (Y === 1'b0)
    );

    // All A inputs high with B1 low and C1 low drives the output high.
    check_all_enables_drive_output_high: assert property (
        @(posedge clk)
        ((C1 === 1'b0) && (A1 === 1'b1) && (A2 === 1'b1) && (A3 === 1'b1) && (B1 === 1'b0))
        |-> (Y === 1'b1)
    );

    // With C1 low, any low A input or high B1 forces the output low.
    check_blocking_conditions_drive_output_low: assert property (
        @(posedge clk)
        ((C1 === 1'b0) &&
         ((A1 === 1'b0) || (A2 === 1'b0) || (A3 === 1'b0) || (B1 === 1'b1)))
        |-> (Y === 1'b0)
    );

    // A high output requires C1 low, all A inputs high, and B1 low.
    check_output_high_requires_enables: assert property (
        @(posedge clk)
        (Y === 1'b1)
        |-> ((C1 === 1'b0) && (A1 === 1'b1) && (A2 === 1'b1) && (A3 === 1'b1) && (B1 === 1'b0))
    );

endmodule