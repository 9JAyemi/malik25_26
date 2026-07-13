module and_gate_ctrl_sva (
    input logic clk,
    input logic A,
    input logic B,
    input logic C1,
    input logic Y
);

    // Y is forced low when C1 is low.
    check_ctrl_low_forces_zero: assert property (
        @(posedge clk) (C1 == 1'b0) |-> (Y == 1'b0)
    );

    // Y matches A&B when C1 is high.
    check_ctrl_high_passes_and: assert property (
        @(posedge clk) (C1 == 1'b1) |-> (Y == (A & B))
    );

    // Y can only be high when C1, A, and B are all high.
    check_output_high_requires_all_high: assert property (
        @(posedge clk) (Y == 1'b1) |-> ((C1 == 1'b1) && (A == 1'b1) && (B == 1'b1))
    );

    // Y is high when C1, A, and B are all high.
    check_all_high_drive_high: assert property (
        @(posedge clk) ((C1 == 1'b1) && (A == 1'b1) && (B == 1'b1)) |-> (Y == 1'b1)
    );

endmodule