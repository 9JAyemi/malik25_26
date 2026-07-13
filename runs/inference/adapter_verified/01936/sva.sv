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

// With ena != 2'b00, q rotates left by 2 bits on the next cycle.
    check_rotate_when_ena_nonzero: assert property (
        @(posedge clk) disable iff (load) (ena != 2'b00) |=> (q == {$past(q[98:0]), $past(q[99:98])})
    );

// With ena == 2'b00, q holds its previous value on the next cycle.
    check_hold_when_ena_zero: assert property (
        @(posedge clk) disable iff (load) (ena == 2'b00) |=> (q == $past(q))
    );

// out_if_else is high exactly when q differs from data.
    check_out_if_else_matches_xor: assert property (
        @(posedge clk) out_if_else == (q != data)
    );

// After load, out_if_else is high because q differs from data.
    check_out_if_else_high_after_load: assert property (
        @(posedge clk) load |=> (out_if_else == 1'b1)
    );

// With ena != 2'b00, out_if_else is low because q equals data after rotation.
    check_out_if_else_low_on_rotate: assert property (
        @(posedge clk) disable iff (load) (ena != 2'b00) |=> (out_if_else == 1'b0)
    );

// With ena == 2'b00, out_if_else is high because q holds its previous value.
    check_out_if_else_high_on_hold: assert property (
        @(posedge clk) disable iff (load) (ena == 2'b00) |=> (out_if_else == 1'b1)
    );

endmodule
