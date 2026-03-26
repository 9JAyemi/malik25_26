module sky130_fd_sc_hd__o211ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1,
    input logic C1
);

    // Y matches the implemented O211AI equation.
    check_function_equation: assert property (
        @(posedge clk) Y == ~(((A1 | A2) & B1) & C1)
    );

    // Y is low when the OR leg, B1, and C1 are all high.
    check_output_low_when_nand_enabled: assert property (
        @(posedge clk) ((A1 | A2) & B1 & C1) |-> (Y == 1'b0)
    );

    // Y is high whenever B1 is low.
    check_output_high_when_b1_low: assert property (
        @(posedge clk) (!B1) |-> (Y == 1'b1)
    );

    // Y is high whenever C1 is low.
    check_output_high_when_c1_low: assert property (
        @(posedge clk) (!C1) |-> (Y == 1'b1)
    );

    // Y is high when both A inputs are low.
    check_output_high_when_or_leg_low: assert property (
        @(posedge clk) ((!A1) & (!A2)) |-> (Y == 1'b1)
    );

    // A1 alone can activate the OR leg and drive Y low with B1 and C1 high.
    check_a1_path_drives_low: assert property (
        @(posedge clk) (A1 & B1 & C1) |-> (Y == 1'b0)
    );

    // A2 alone can activate the OR leg and drive Y low with B1 and C1 high.
    check_a2_path_drives_low: assert property (
        @(posedge clk) (A2 & B1 & C1) |-> (Y == 1'b0)
    );

endmodule