module shift_reg_sva (
    input logic [3:0] data_in,
    input logic       load,
    input logic       clk,
    input logic [3:0] q
);

    // On a load cycle, q must capture data_in by the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (q == $past(data_in))
    );

    // On a non-load cycle, q must rotate left by one bit by the next clock.
    check_shift_rotates_q: assert property (
        @(posedge clk) !load |=> (q == { $past(q[2]), $past(q[1]), $past(q[0]), $past(q[3]) })
    );

    // Every cycle, q must follow the RTL next-state function from the prior cycle.
    check_next_state_function: assert property (
        @(posedge clk) 1'b1 |=> (q == ($past(load) ? $past(data_in)
                                                 : { $past(q[2]), $past(q[1]), $past(q[0]), $past(q[3]) }))
    );

    // During a shift, q[3] must take the previous q[2].
    check_shift_bit3_mapping: assert property (
        @(posedge clk) !load |=> (q[3] == $past(q[2]))
    );

    // During a shift, q[2] must take the previous q[1].
    check_shift_bit2_mapping: assert property (
        @(posedge clk) !load |=> (q[2] == $past(q[1]))
    );

    // During a shift, q[1] must take the previous q[0].
    check_shift_bit1_mapping: assert property (
        @(posedge clk) !load |=> (q[1] == $past(q[0]))
    );

    // During a shift, q[0] must wrap from the previous q[3].
    check_shift_bit0_mapping: assert property (
        @(posedge clk) !load |=> (q[0] == $past(q[3]))
    );

endmodule