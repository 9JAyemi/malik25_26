module shift_register_sva (
    input logic clk,
    input logic load,
    input logic [3:0] data,
    input logic [3:0] out
);
    // Clock: clk; no reset present in RTL.
    // Sequential behavior: on posedge clk, if load=1 load data; else shift left and insert data[3] at LSB.

    // Next-cycle out matches RTL next-state function based on prior cycle inputs.
    check_next_state_function: assert property (
        @(posedge clk) 1'b1 |=> (out == ($past(load) ? $past(data) : {$past(out[2:0]), $past(data[3])}))
    );

    // When load is 1, next-cycle out equals prior-cycle data.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (out == $past(data))
    );

    // When load is 0, next-cycle out equals prior out shifted with prior data[3] into LSB.
    check_shift_concat: assert property (
        @(posedge clk) !load |=> (out == {$past(out[2:0]), $past(data[3])})
    );

    // In shift mode, upper bits move from lower bits of prior out.
    check_shift_upper_bits_move: assert property (
        @(posedge clk) !load |=> (out[3:1] == $past(out[2:0]))
    );

    // In shift mode, LSB becomes prior-cycle data[3].
    check_shift_lsb_source: assert property (
        @(posedge clk) !load |=> (out[0] == $past(data[3]))
    );

endmodule