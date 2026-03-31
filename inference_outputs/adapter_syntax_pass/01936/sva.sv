module xor_shift_register_sva (
    input logic clk,
    input logic load,
    input logic [1:0] ena,
    input logic [99:0] data,
    input logic [99:0] q,
    input logic out_if_else
);

    // q captures data on the next cycle when load is asserted.
    check_load_captures_data: assert property (
        @(posedge clk) load |=> (q == $past(data))
    );

    // q holds its value when load is deasserted.
    check_hold_when_not_loading: assert property (
        @(posedge clk) !load |=> (q == $past(q))
    );

    // q rotates right by two bits when enabled and not loading.
    check_rotate_when_enabled: assert property (
        @(posedge clk) (!load && (ena != 2'b00)) |=> (q == {$past(q[97:0]), $past(q[99:98])})
    );

    // q holds its value when enabled and not loading.
    check_hold_when_enabled: assert property (
        @(posedge clk) (!load && (ena == 2'b00)) |=> (q == $past(q))
    );

    // out_if_else is high whenever q differs from data.
    check_out_if_else_high_when_q_differs_from_data: assert property (
        @(posedge clk) (q != data) |-> (out_if_else == 1'b1)
    );

    // out_if_else is low whenever q matches data.
    check_out_if_else_low_when_q_matches_data: assert property (
        @(posedge clk) (q == data) |-> (out_if_else == 1'b0)
    );

endmodule