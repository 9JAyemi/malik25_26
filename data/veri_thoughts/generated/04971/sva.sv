module nand4_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic y
);

    // Sample the combinational DUT on an external clock; the RTL has no reset.

    // Output must implement a 4-input NAND.
    check_y_matches_nand_function: assert property (
        @(posedge clk) y == ~(a & b & c & d)
    );

    // All inputs high forces the output low.
    check_all_inputs_high_drive_y_low: assert property (
        @(posedge clk) (a & b & c & d) |-> (y == 1'b0)
    );

    // A low output only occurs when all inputs are high.
    check_y_low_only_when_all_inputs_high: assert property (
        @(posedge clk) (y == 1'b0) |-> (a & b & c & d)
    );

    // Any low input forces the output high.
    check_any_input_low_drives_y_high: assert property (
        @(posedge clk) (!(a & b & c & d)) |-> (y == 1'b1)
    );

    // Stable inputs keep the output stable.
    check_stable_inputs_keep_y_stable: assert property (
        @(posedge clk) $stable({a, b, c, d}) |-> $stable(y)
    );

endmodule