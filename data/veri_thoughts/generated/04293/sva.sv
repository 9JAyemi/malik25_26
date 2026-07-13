module four_input_one_output_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out
);

    // Input a HIGH drives the output HIGH.
    check_a_drives_out_high: assert property (
        @(posedge clk) (a == 1'b1) |-> (out == 1'b1)
    );

    // Input b HIGH drives the output HIGH.
    check_b_drives_out_high: assert property (
        @(posedge clk) (b == 1'b1) |-> (out == 1'b1)
    );

    // Input c HIGH drives the output HIGH.
    check_c_drives_out_high: assert property (
        @(posedge clk) (c == 1'b1) |-> (out == 1'b1)
    );

    // Input d HIGH drives the output HIGH.
    check_d_drives_out_high: assert property (
        @(posedge clk) (d == 1'b1) |-> (out == 1'b1)
    );

    // When all inputs are LOW, the output is LOW.
    check_all_inputs_low_drive_out_low: assert property (
        @(posedge clk)
        ((a == 1'b0) && (b == 1'b0) && (c == 1'b0) && (d == 1'b0)) |-> (out == 1'b0)
    );

    // Output equals the OR of the four inputs.
    check_out_matches_or_of_inputs: assert property (
        @(posedge clk) (out == (a || b || c || d))
    );

endmodule