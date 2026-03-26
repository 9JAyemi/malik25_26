module mux2_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic q
);

    // When b is 1, q follows a.
    check_b_high_selects_a: assert property (
        @(posedge clk) (b === 1'b1) |-> (q === a)
    );

    // When b is not 1, q follows b.
    check_b_not_high_selects_b: assert property (
        @(posedge clk) (b !== 1'b1) |-> (q === b)
    );

    // When b is 0, q is 0.
    check_b_low_forces_q_low: assert property (
        @(posedge clk) (b === 1'b0) |-> (q === 1'b0)
    );

    // When both a and b are 1, q is 1.
    check_a_and_b_high_drive_q_high: assert property (
        @(posedge clk) ((a === 1'b1) && (b === 1'b1)) |-> (q === 1'b1)
    );

    // When a is 0 and b is 1, q is 0.
    check_a_low_with_b_high_drives_q_low: assert property (
        @(posedge clk) ((a === 1'b0) && (b === 1'b1)) |-> (q === 1'b0)
    );

    // q can only be 1 when both inputs are 1.
    check_q_high_implies_a_and_b_high: assert property (
        @(posedge clk) (q === 1'b1) |-> ((a === 1'b1) && (b === 1'b1))
    );

endmodule