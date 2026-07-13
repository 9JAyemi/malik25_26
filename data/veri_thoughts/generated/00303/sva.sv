module xor_adder_sva (
    input logic       clk,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic [1:0] sum
);

    // Sum captures the previous cycle XOR of a and b.
    check_sum_registers_prev_xor: assert property (
        @(posedge clk) 1'b1 |=> (sum == ($past(a) ^ $past(b)))
    );

    // Equal inputs produce a zero sum on the next clock.
    check_equal_inputs_produce_zero: assert property (
        @(posedge clk) (a == b) |=> (sum == 2'b00)
    );

    // A zero a input passes b through to sum on the next clock.
    check_zero_a_passthrough_b: assert property (
        @(posedge clk) (a == 2'b00) |=> (sum == $past(b))
    );

    // A zero b input passes a through to sum on the next clock.
    check_zero_b_passthrough_a: assert property (
        @(posedge clk) (b == 2'b00) |=> (sum == $past(a))
    );

endmodule