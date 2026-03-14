module and_gate_sva (
    input logic clk,
    input logic X,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic B2,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Output equals bitwise AND of all four inputs.
    check_output_equals_and4: assert property (
        @(posedge clk) X == (A1 & A2 & B1 & B2)
    );

    // X can be 1 only when all inputs are 1.
    check_x_implies_all_ones: assert property (
        @(posedge clk) (X == 1'b1) |-> (A1 & A2 & B1 & B2)
    );

    // X must be 0 when A1 is 0.
    check_low_if_A1_zero: assert property (
        @(posedge clk) (A1 == 1'b0) |-> (X == 1'b0)
    );

    // X must be 0 when A2 is 0.
    check_low_if_A2_zero: assert property (
        @(posedge clk) (A2 == 1'b0) |-> (X == 1'b0)
    );

    // X must be 0 when B1 is 0.
    check_low_if_B1_zero: assert property (
        @(posedge clk) (B1 == 1'b0) |-> (X == 1'b0)
    );

    // X must be 0 when B2 is 0.
    check_low_if_B2_zero: assert property (
        @(posedge clk) (B2 == 1'b0) |-> (X == 1'b0)
    );

    // A rising edge on X only occurs when all inputs are 1.
    check_rose_x_requires_all_ones: assert property (
        @(posedge clk) $rose(X) |-> (A1 & A2 & B1 & B2)
    );

    // A falling edge on X only occurs when at least one input is 0.
    check_fell_x_requires_any_zero: assert property (
        @(posedge clk) $fell(X) |-> !(A1 & A2 & B1 & B2)
    );

    // X cannot change unless one of the inputs changed.
    check_x_change_requires_input_change: assert property (
        @(posedge clk) $changed(X) |-> ($changed(A1) || $changed(A2) || $changed(B1) || $changed(B2))
    );
endmodule