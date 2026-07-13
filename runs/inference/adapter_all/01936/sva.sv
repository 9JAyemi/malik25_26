module xor_shift_register_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [99:0] data,
    input logic [99:0] q,
    input logic out_if_else
);

    // Load captures data into q on the next cycle.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (q == $past(data))
    );

    // With ena != 2'b00, q rotates left by two bits on the next cycle.
    check_rotate_when_enabled: assert property (
        @(posedge clk) (!load && (ena != 2'b00)) |=> (q == {$past(q[98:0]), $past(q[99:98])})
    );

    // With ena == 2'b00, q holds its value on the next cycle.
    check_hold_when_disabled: assert property (
        @(posedge clk) (!load && (ena == 2'b00)) |=> (q == $past(q))
    );

    // out_if_else is high when q differs from data.
    check_out_if_else_high_when_mismatch: assert property (
        @(posedge clk) (q != data) |-> (out_if_else == 1'b1)
    );

    // out_if_else is low when q matches data.
    check_out_if_else_low_when_match: assert property (
        @(posedge clk) (q == data) |-> (out_if_else == 1'b0)
    );

    // out_if_else matches the XOR of q and data.
    check_out_if_else_matches_xor: assert property (
        @(posedge clk) (out_if_else == (q ^ data))
    );

endmodule