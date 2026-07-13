module shift_register_sva (
    input logic clk,
    input logic [3:0] data_in,
    input logic [3:0] data_out
);

    // data_out reflects data_in sampled four clocks earlier.
    check_output_is_4_cycle_delayed_input: assert property (
        @(posedge clk)
        (!$initstate &&
         !$past($initstate) &&
         !$past($initstate, 2) &&
         !$past($initstate, 3) &&
         !$past($initstate, 4))
        |-> (data_out == $past(data_in, 4))
    );

    // Unchanged delayed input samples keep data_out unchanged across cycles.
    check_output_stable_when_delayed_input_stable: assert property (
        @(posedge clk)
        (!$initstate &&
         !$past($initstate) &&
         !$past($initstate, 2) &&
         !$past($initstate, 3) &&
         !$past($initstate, 4) &&
         !$past($initstate, 5) &&
         ($past(data_in, 4) == $past(data_in, 5)))
        |-> (data_out == $past(data_out))
    );

    // Changed delayed input samples cause data_out to change across cycles.
    check_output_changes_when_delayed_input_changes: assert property (
        @(posedge clk)
        (!$initstate &&
         !$past($initstate) &&
         !$past($initstate, 2) &&
         !$past($initstate, 3) &&
         !$past($initstate, 4) &&
         !$past($initstate, 5) &&
         ($past(data_in, 4) != $past(data_in, 5)))
        |-> (data_out != $past(data_out))
    );

    // A constant input over five sampled clocks appears unchanged at the output.
    check_constant_input_reaches_output: assert property (
        @(posedge clk)
        (!$initstate &&
         !$past($initstate) &&
         !$past($initstate, 2) &&
         !$past($initstate, 3) &&
         !$past($initstate, 4) &&
         (data_in == $past(data_in)) &&
         (data_in == $past(data_in, 2)) &&
         (data_in == $past(data_in, 3)) &&
         (data_in == $past(data_in, 4)))
        |-> (data_out == data_in)
    );

endmodule