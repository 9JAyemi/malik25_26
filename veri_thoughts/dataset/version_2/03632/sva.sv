module shift_register_sva (
    input logic clk,
    input logic load,
    input logic control,
    input logic [7:0] data_in,
    input logic [7:0] data_out
);

    // Load copies data_in into the register on the next clock.
    check_load_copies_input: assert property (
        @(posedge clk)
        load |=> (data_out == $past(data_in))
    );

    // With load low and control high, the register rotates left by one bit.
    check_shift_left_rotate: assert property (
        @(posedge clk)
        (!load && control) |=> (data_out == {$past(data_out[6:0]), $past(data_out[7])})
    );

    // With load low and control low, the register rotates right by one bit.
    check_shift_right_rotate: assert property (
        @(posedge clk)
        (!load && !control) |=> (data_out == {$past(data_out[0]), $past(data_out[7:1])})
    );

    // Every clock follows the RTL next-state update function.
    check_next_state_function: assert property (
        @(posedge clk)
        1'b1 |=> (
            data_out == (
                $past(load) ? $past(data_in) :
                ($past(control) ? {$past(data_out[6:0]), $past(data_out[7])}
                                : {$past(data_out[0]), $past(data_out[7:1])})
            )
        )
    );

endmodule