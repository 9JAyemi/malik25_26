module my_module_assertions (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);

    // Y must implement a 4-input NAND of A1, A2, B1, and B2.
    check_nand_function: assert property (
        @(posedge clk) Y === ~(A1 & A2 & B1 & B2)
    );

    // When all four inputs are high, Y must be low.
    check_all_high_forces_low: assert property (
        @(posedge clk) (A1 && A2 && B1 && B2) |-> (Y === 1'b0)
    );

    // If any input is low, Y must be high.
    check_any_low_forces_high: assert property (
        @(posedge clk) (!A1 || !A2 || !B1 || !B2) |-> (Y === 1'b1)
    );

    // Y can be low only when all four inputs are high.
    check_output_low_only_when_all_high: assert property (
        @(posedge clk) (Y === 1'b0) |-> (A1 && A2 && B1 && B2)
    );

    // Y can be high only when at least one input is low.
    check_output_high_only_when_any_low: assert property (
        @(posedge clk) (Y === 1'b1) |-> (!A1 || !A2 || !B1 || !B2)
    );

endmodule