module sky130_fd_sc_hd__o311ai_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic Y,
    input logic VPB,
    input logic VPWR,
    input logic VGND,
    input logic VNB
);

    // Y follows the implemented combinational equation.
    check_output_equation: assert property (
        @(posedge clk)
        Y == (A1 || (A2 && !A1) || (A3 && !A2 && !A1))
    );

    // A1 asserted drives Y high.
    check_a1_drives_y_high: assert property (
        @(posedge clk)
        A1 |-> Y
    );

    // With A1 low, A2 asserted drives Y high.
    check_a2_drives_y_high_when_a1_low: assert property (
        @(posedge clk)
        (!A1 && A2) |-> Y
    );

    // With A1 and A2 low, A3 asserted drives Y high.
    check_a3_drives_y_high_when_a1_a2_low: assert property (
        @(posedge clk)
        (!A1 && !A2 && A3) |-> Y
    );

    // When all contributing inputs are low, Y is low.
    check_all_inputs_low_drives_y_low: assert property (
        @(posedge clk)
        (!A1 && !A2 && !A3) |-> !Y
    );

    // A high Y requires at least one of A1, A2, or A3 high.
    check_y_high_requires_active_input: assert property (
        @(posedge clk)
        Y |-> (A1 || A2 || A3)
    );

    // A low Y requires all of A1, A2, and A3 low.
    check_y_low_requires_all_inputs_low: assert property (
        @(posedge clk)
        !Y |-> (!A1 && !A2 && !A3)
    );

endmodule