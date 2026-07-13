module sky130_fd_sc_ls__or2_sva (
    input logic clk,
    input logic X,
    input logic A,
    input logic B
);

    // Output matches the OR of the two inputs.
    check_or_function: assert property (
        @(posedge clk) X == (A | B)
    );

    // Both inputs low forces the output low.
    check_both_low_drive_low: assert property (
        @(posedge clk) (!A && !B) |-> (X == 1'b0)
    );

    // A high input forces the output high.
    check_a_high_drives_high: assert property (
        @(posedge clk) A |-> (X == 1'b1)
    );

    // B high input forces the output high.
    check_b_high_drives_high: assert property (
        @(posedge clk) B |-> (X == 1'b1)
    );

    // A low output implies both inputs are low.
    check_low_output_requires_low_inputs: assert property (
        @(posedge clk) !X |-> (!A && !B)
    );

endmodule