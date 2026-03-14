module sequence_detector_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic Y,
    input logic clk
);

    ///// Output Y behavior w.r.t. D while in ABC_STATE (Y==1) /////
    // If Y is HIGH and D is LOW, Y stays HIGH next cycle.
    check_y_holds_when_D_low: assert property (
        @(posedge clk) (Y && (D == 1'b0)) |=> (Y == 1'b1)
    );

    // If Y is HIGH and D is HIGH, Y goes LOW next cycle.
    check_y_clears_on_D_high: assert property (
        @(posedge clk) (Y && (D == 1'b1)) |=> (Y == 1'b0)
    );

    ///// Change constraints for Y /////
    // Y cannot fall unless D was HIGH in the prior cycle.
    check_y_no_fall_without_D: assert property (
        @(posedge clk) (D == 1'b0) |=> (!$fell(Y))
    );

    // Y cannot rise unless C was HIGH in the prior cycle.
    check_y_no_rise_without_C: assert property (
        @(posedge clk) (C == 1'b0) |=> (!$rose(Y))
    );

    // When both C and D are LOW, Y does not change next cycle.
    check_y_stable_when_C_D_low: assert property (
        @(posedge clk) ((C == 1'b0) && (D == 1'b0)) |=> $stable(Y)
    );

    // If Y is LOW and C is LOW, it stays LOW next cycle (cannot enter ABC without C).
    check_y_low_holds_when_C_low: assert property (
        @(posedge clk) ((Y == 1'b0) && (C == 1'b0)) |=> (Y == 1'b0)
    );

endmodule