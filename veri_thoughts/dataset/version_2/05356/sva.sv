module or_nand_buffer_sva (
    input logic clk,
    input logic Y,
    input logic A1,
    input logic A2,
    input logic B1
);

    // Y must equal the buffered NAND of (A1 OR A2) and B1.
    check_boolean_function: assert property (
        @(posedge clk) Y == ~((A1 | A2) & B1)
    );

    // A low B1 forces the NAND output high.
    check_b1_low_forces_y_high: assert property (
        @(posedge clk) (!B1) |-> (Y == 1'b1)
    );

    // Low A1 and A2 force the OR term low and Y high.
    check_no_or_input_forces_y_high: assert property (
        @(posedge clk) ((!A1) && (!A2)) |-> (Y == 1'b1)
    );

    // A high B1 with either OR input high drives Y low.
    check_active_inputs_drive_y_low: assert property (
        @(posedge clk) (B1 && (A1 || A2)) |-> (Y == 1'b0)
    );

    // A low Y requires B1 high and at least one OR input high.
    check_y_low_has_valid_cause: assert property (
        @(posedge clk) (Y == 1'b0) |-> (B1 && (A1 || A2))
    );

endmodule