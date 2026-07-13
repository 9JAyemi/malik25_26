module binary_operation_and_counter_sva (
    input logic clk,
    input logic reset,
    input logic up_down,
    input logic load,
    input logic [3:0] load_data,
    input logic [2:0] a,
    input logic [2:0] b,
    input logic [2:0] out_and_bitwise,
    input logic out_and_logical,
    input logic [2:0] out_xor,
    input logic [5:0] out_not,
    input logic [3:0] q
);

    // Reset drives the counter output to zero.
    check_reset_clears_q: assert property (
        @(posedge clk) !reset |-> (q == 4'd0)
    );

    // Load updates the counter on the next clock and overrides direction.
    check_load_updates_q: assert property (
        @(posedge clk) disable iff (!reset)
        load |=> (q == $past(load_data))
    );

    // When not loading, up_down high increments the counter.
    check_count_increment: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && up_down) |=> (q == ($past(q) + 4'd1))
    );

    // When not loading, up_down low decrements the counter.
    check_count_decrement: assert property (
        @(posedge clk) disable iff (!reset)
        (!load && !up_down) |=> (q == ($past(q) - 4'd1))
    );

    // Bitwise AND output matches a & b.
    check_out_and_bitwise: assert property (
        @(posedge clk) disable iff (!reset)
        (out_and_bitwise == (a & b))
    );

    // Logical AND output is high only when both operands are non-zero.
    check_out_and_logical: assert property (
        @(posedge clk) disable iff (!reset)
        (out_and_logical == ((a != 3'd0) && (b != 3'd0)))
    );

    // XOR output matches a ^ b.
    check_out_xor: assert property (
        @(posedge clk) disable iff (!reset)
        (out_xor == (a ^ b))
    );

    // NOT output matches inversion of the concatenated operands.
    check_out_not: assert property (
        @(posedge clk) disable iff (!reset)
        (out_not == ~{a, b})
    );

endmodule