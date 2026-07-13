module barrel_shifter_sva (
    input logic [15:0] in,
    input logic [3:0]  shift_amt,
    input logic        shift_left,
    input logic [15:0] out
);

    // In left-shift mode, out equals in shifted left by shift_amt.
    check_left_shift_behavior: assert property (
        @($global_clock) shift_left |-> (out == (in << shift_amt))
    );

    // In right-shift mode, out equals in shifted right by shift_amt.
    check_right_shift_behavior: assert property (
        @($global_clock) !shift_left |-> (out == (in >> shift_amt))
    );

    // A zero shift amount leaves the input unchanged.
    check_zero_shift_passthrough: assert property (
        @($global_clock) (shift_amt == 4'd0) |-> (out == in)
    );

    // A zero input always produces a zero output.
    check_zero_input_zero_output: assert property (
        @($global_clock) (in == 16'd0) |-> (out == 16'd0)
    );

    // The output always matches the selected barrel-shift function.
    check_output_matches_selected_shift: assert property (
        @($global_clock) (out == (shift_left ? (in << shift_amt) : (in >> shift_amt)))
    );

endmodule