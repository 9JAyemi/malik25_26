module top_sva (
    input logic [3:0] di,
    input logic \do
);

    // Clockless combinational DUT sampled on the formal global clock.

    // Output matches the implemented boolean function.
    check_output_function: assert property (
        @($global_clock)
        \do == ((di[1] | di[0]) & (di[3] | di[2]))
    );

    // A zero lower pair forces the output low.
    check_lower_pair_zero_forces_low: assert property (
        @($global_clock)
        (di[1:0] == 2'b00) |-> (\do == 1'b0)
    );

    // A zero upper pair forces the output low.
    check_upper_pair_zero_forces_low: assert property (
        @($global_clock)
        (di[3:2] == 2'b00) |-> (\do == 1'b0)
    );

    // One asserted bit in each pair drives the output high.
    check_one_in_each_pair_drives_high: assert property (
        @($global_clock)
        ((di[1] | di[0]) & (di[3] | di[2])) |-> (\do == 1'b1)
    );

    // All-zero input drives the output low.
    check_all_zero_input_drives_low: assert property (
        @($global_clock)
        (di == 4'b0000) |-> (\do == 1'b0)
    );

    // All-one input drives the output high.
    check_all_one_input_drives_high: assert property (
        @($global_clock)
        (di == 4'b1111) |-> (\do == 1'b1)
    );

endmodule