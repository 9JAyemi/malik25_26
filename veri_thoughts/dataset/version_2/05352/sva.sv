module rotator_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [99:0] data,
    input logic [99:0] q
);

    // Load captures data into q on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (q == $past(data))
    );

    // With ena=00 and no load, q holds its previous value.
    check_hold_when_ena_zero: assert property (
        @(posedge clk) (!load && (ena == 2'b00)) |=> (q == $past(q))
    );

    // With ena=01 and no load, q rotates left by one bit.
    check_rotate_left: assert property (
        @(posedge clk) (!load && (ena == 2'b01)) |=> (q == { $past(q[98:0]), $past(q[99]) })
    );

    // With ena=10 and no load, q rotates right by one bit.
    check_rotate_right: assert property (
        @(posedge clk) (!load && (ena == 2'b10)) |=> (q == { $past(q[0]), $past(q[99:1]) })
    );

    // With ena=11 and no load, q holds because no assignment occurs.
    check_hold_when_ena_three: assert property (
        @(posedge clk) (!load && (ena == 2'b11)) |=> (q == $past(q))
    );

    // A left rotation followed by a right rotation restores q.
    check_left_then_right_restore: assert property (
        @(posedge clk) (!load && (ena == 2'b01)) ##1 (!load && (ena == 2'b10)) |=> (q == $past(q,2))
    );

    // A right rotation followed by a left rotation restores q.
    check_right_then_left_restore: assert property (
        @(posedge clk) (!load && (ena == 2'b10)) ##1 (!load && (ena == 2'b01)) |=> (q == $past(q,2))
    );

endmodule