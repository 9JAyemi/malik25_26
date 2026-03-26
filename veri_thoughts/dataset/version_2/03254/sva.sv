module logic_or_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic O
);

    // Output equals the OR of the three inputs.
    check_output_matches_or: assert property (
        @(posedge clk) O == (A1 | A2 | A3)
    );

    // Output is low when all inputs are low.
    check_all_inputs_low_drives_output_low: assert property (
        @(posedge clk) (!(A1 | A2 | A3)) |-> (!O)
    );

    // A high A1 input forces the output high.
    check_a1_high_drives_output_high: assert property (
        @(posedge clk) A1 |-> O
    );

    // A high A2 input forces the output high.
    check_a2_high_drives_output_high: assert property (
        @(posedge clk) A2 |-> O
    );

    // A high A3 input forces the output high.
    check_a3_high_drives_output_high: assert property (
        @(posedge clk) A3 |-> O
    );

endmodule