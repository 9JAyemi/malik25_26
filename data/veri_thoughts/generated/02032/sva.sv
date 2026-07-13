module sky130_fd_sc_ms__o21ai_sva (
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic VPWR,
    input logic VGND,
    input logic VPB,
    input logic VNB
);
    // Combinational cell; no clock/reset in RTL. Sample on any input/output edge.

    // Y implements ~(B1 & (A1 | A2)).
    check_o21ai_function: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            Y === ~(B1 & (A1 | A2))
    );

    // Y low implies B1 is 1 and at least one of A1/A2 is 1.
    check_y_low_implies_inputs_active: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            (Y === 1'b0) |-> (B1 === 1'b1) && ((A1 === 1'b1) || (A2 === 1'b1))
    );

    // If B1 is 0 then Y must be 1.
    check_b1_low_forces_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            (B1 === 1'b0) |-> (Y === 1'b1)
    );

    // If both A1 and A2 are 0 then Y must be 1.
    check_both_a_low_force_y_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ((A1 === 1'b0) && (A2 === 1'b0)) |-> (Y === 1'b1)
    );

    // If B1 is 1 and either A1 or A2 is 1 then Y must be 0.
    check_and_path_forces_y_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            ((B1 === 1'b1) && ((A1 === 1'b1) || (A2 === 1'b1))) |-> (Y === 1'b0)
    );

    // Y high implies B1 is 0 or both A1 and A2 are 0.
    check_y_high_implies_inputs_inactive: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            (Y === 1'b1) |-> ((B1 === 1'b0) || ((A1 === 1'b0) && (A2 === 1'b0)))
    );

    // With known inputs (no X/Z), Y must be known (no X/Z).
    check_no_x_when_inputs_known: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1 or posedge Y or negedge Y)
            (!$isunknown({A1,A2,B1})) |-> (!$isunknown(Y))
    );

endmodule