module three_input_gate_sva (
    input logic A1,
    input logic A2,
    input logic B1,
    input logic X
);

    // No clock or reset is present in the RTL.
    // The logic is purely combinational: X is high only when A1, A2, and B1 are all high.

    // On an input edge, any low input requires X low.
    check_any_low_drives_x_low: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (!A1 || !A2 || !B1) |-> !X
    );

    // On an input edge, all high inputs require X high.
    check_all_high_drives_x_high: assert property (
        @(posedge A1 or negedge A1 or posedge A2 or negedge A2 or posedge B1 or negedge B1)
        (A1 && A2 && B1) |-> X
    );

    // X can rise only when all three inputs are high.
    check_x_rises_only_for_all_high: assert property (
        @(posedge X)
        (A1 && A2 && B1)
    );

    // X can fall only when at least one input is low.
    check_x_falls_only_when_input_low: assert property (
        @(negedge X)
        (!A1 || !A2 || !B1)
    );

endmodule