module sky130_fd_sc_ms__o31ai_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1
);

    // External sampling clock; RTL has no native clock or reset.

    // Y matches the implemented O31AI combinational function.
    check_logic_function: assert property (
        @(posedge clk) disable iff (1'b0)
        Y == ~(B1 & (A1 | A2 | A3))
    );

    // B1 low forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (B1 == 1'b0) |-> (Y == 1'b1)
    );

    // All A inputs low force the OR term low and Y high.
    check_all_a_low_forces_y_high: assert property (
        @(posedge clk) disable iff (1'b0)
        ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0)) |-> (Y == 1'b1)
    );

    // B1 high with any A input high forces Y low.
    check_b1_and_any_a_high_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B1 == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))) |-> (Y == 1'b0)
    );

    // A low Y requires B1 to be high.
    check_y_low_requires_b1_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b0) |-> (B1 == 1'b1)
    );

    // A low Y requires at least one A input to be high.
    check_y_low_requires_any_a_high: assert property (
        @(posedge clk) disable iff (1'b0)
        (Y == 1'b0) |-> ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))
    );

    // If Y is high while B1 is high, all A inputs must be low.
    check_y_high_with_b1_high_requires_all_a_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((Y == 1'b1) && (B1 == 1'b1)) |-> ((A1 == 1'b0) && (A2 == 1'b0) && (A3 == 1'b0))
    );

    // If Y is high while any A input is high, B1 must be low.
    check_y_high_with_any_a_high_requires_b1_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((Y == 1'b1) && ((A1 == 1'b1) || (A2 == 1'b1) || (A3 == 1'b1))) |-> (B1 == 1'b0)
    );

    // B1 and A1 high are sufficient to drive Y low.
    check_b1_and_a1_high_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B1 == 1'b1) && (A1 == 1'b1)) |-> (Y == 1'b0)
    );

    // B1 and A2 high are sufficient to drive Y low.
    check_b1_and_a2_high_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B1 == 1'b1) && (A2 == 1'b1)) |-> (Y == 1'b0)
    );

    // B1 and A3 high are sufficient to drive Y low.
    check_b1_and_a3_high_forces_y_low: assert property (
        @(posedge clk) disable iff (1'b0)
        ((B1 == 1'b1) && (A3 == 1'b1)) |-> (Y == 1'b0)
    );

endmodule