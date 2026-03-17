module phase_detector_assertions (
    input logic clk,
    input logic \ref ,
    input logic in,
    input logic error
);

property p_error_matches_sampled_xor;
    logic ref_sampled, in_sampled;
    @(posedge clk)
        (1'b1, ref_sampled = \ref , in_sampled = in)
        |-> ##2 (error == (ref_sampled ^ in_sampled));
endproperty

// Error equals the XOR of ref and in sampled two clocks earlier.
check_error_matches_sampled_xor: assert property (p_error_matches_sampled_xor);

// Equal sampled inputs drive error low two clocks later.
check_equal_inputs_drive_zero: assert property (
    @(posedge clk) (\ref  == in) |-> ##2 (error == 1'b0)
);

// Different sampled inputs drive error high two clocks later.
check_different_inputs_drive_one: assert property (
    @(posedge clk) (\ref  != in) |-> ##2 (error == 1'b1)
);

// Stable inputs produce a stable error two clocks later.
check_stable_inputs_hold_error: assert property (
    @(posedge clk) ($stable(\ref ) && $stable(in)) |-> ##2 $stable(error)
);

// A toggle on exactly one input causes error to toggle two clocks later.
check_single_input_toggle_toggles_error: assert property (
    @(posedge clk)
        (($changed(\ref ) && $stable(in)) || ($stable(\ref ) && $changed(in)))
        |-> ##2 $changed(error)
);

// Simultaneous toggles on both inputs keep the XOR result unchanged two clocks later.
check_both_inputs_toggle_hold_error: assert property (
    @(posedge clk) ($changed(\ref ) && $changed(in)) |-> ##2 $stable(error)
);

endmodule