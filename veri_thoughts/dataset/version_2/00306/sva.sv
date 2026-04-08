module rotator_sva (
    input logic         clk,
    input logic         load,
    input logic [1:0]   ena,
    input logic [99:0]  data,
    input logic [99:0]  q
);

    // load captures data into q on the next clock.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (q == $past(data))
    );

    // when load is low and ena[0] is set, q rotates right by one.
    check_rotate_right_one_on_ena0: assert property (
        @(posedge clk) (!load && ena[0]) |=> (q == { $past(q[0]), $past(q[99:1]) })
    );

    // when load is low and only ena[1] is set, q rotates left by one.
    check_rotate_left_one_on_ena1_only: assert property (
        @(posedge clk) (!load && !ena[0] && ena[1]) |=> (q == { $past(q[98:0]), $past(q[99]) })
    );

    // when load is low and ena is zero, q holds its value.
    check_hold_when_ena_zero: assert property (
        @(posedge clk) (!load && (ena == 2'b00)) |=> (q == $past(q))
    );

    // when both enable bits are set, the first ena[0] branch still wins.
    check_both_enable_bits_rotate_right_one: assert property (
        @(posedge clk) (!load && (ena == 2'b11)) |=> (q == { $past(q[0]), $past(q[99:1]) })
    );

endmodule