module seven_input_one_output_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic e,
    input logic f,
    input logic g,
    input logic x
);

    // x must equal the AND of all seven inputs.
    check_x_matches_all_inputs_and: assert property (
        @(posedge clk) x == (a & b & c & d & e & f & g)
    );

    // All seven high must drive x high.
    check_all_inputs_high_drive_x_high: assert property (
        @(posedge clk) (a & b & c & d & e & f & g) |-> x
    );

    // Any low input must drive x low.
    check_any_low_input_drives_x_low: assert property (
        @(posedge clk) !(a & b & c & d & e & f & g) |-> !x
    );

endmodule