module sky130_fd_sc_hdll__nor4_sva (
    input logic clk,
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic D
);

    // No clock or reset exists in the RTL; sample the combinational function on clk.

    // Y must equal the 4-input NOR of A, B, C, and D.
    check_nor_function: assert property (
        @(posedge clk) (Y == ~(A | B | C | D))
    );

    // If all inputs are low, Y must be high.
    check_all_inputs_low_drives_high: assert property (
        @(posedge clk) ((!A && !B && !C && !D) |-> (Y == 1'b1))
    );

    // If any input is high, Y must be low.
    check_any_input_high_drives_low: assert property (
        @(posedge clk) ((A || B || C || D) |-> (Y == 1'b0))
    );

endmodule