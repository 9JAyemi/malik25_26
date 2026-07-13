module binary_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic clk,
    input logic rst_n,
    input logic [3:0] S,
    input logic Cout
);

    // During active-low reset, the registered outputs are cleared.
    check_reset_clears_outputs: assert property (
        @(posedge clk) (!rst_n) |-> ({Cout, S} == 5'b0)
    );

    // A sampled reset cycle leaves the outputs cleared at the next sampled clock.
    check_reset_keeps_outputs_cleared_next_cycle: assert property (
        @(posedge clk) (!rst_n) |=> ({Cout, S} == 5'b0)
    );

    // On active cycles, the next sampled output is either the registered sum or the reset value.
    check_next_output_is_sum_or_reset_value: assert property (
        @(posedge clk) disable iff (!rst_n)
        1'b1 |=> (({Cout, S} == 5'b0) ||
                  ({Cout, S} == $past({1'b0, A} + {1'b0, B} + Cin)))
    );

    // With B and Cin low, the next sampled output is either A or the reset value.
    check_b_zero_cin_zero_passthrough_or_reset: assert property (
        @(posedge clk) disable iff (!rst_n)
        (B == 4'b0 && Cin == 1'b0) |=> (({Cout, S} == 5'b0) ||
                                        ({Cout, S} == {1'b0, $past(A)}))
    );

    // With A and Cin low, the next sampled output is either B or the reset value.
    check_a_zero_cin_zero_passthrough_or_reset: assert property (
        @(posedge clk) disable iff (!rst_n)
        (A == 4'b0 && Cin == 1'b0) |=> (({Cout, S} == 5'b0) ||
                                        ({Cout, S} == {1'b0, $past(B)}))
    );

    // Zero inputs must produce a zero registered output.
    check_zero_inputs_produce_zero_output: assert property (
        @(posedge clk) disable iff (!rst_n)
        (A == 4'b0 && B == 4'b0 && Cin == 1'b0) |=> ({Cout, S} == 5'b0)
    );

    // Any non-overflowing addition must register a low carry.
    check_no_overflow_keeps_carry_low: assert property (
        @(posedge clk) disable iff (!rst_n)
        (({1'b0, A} + {1'b0, B} + Cin) <= 5'd15) |=> (Cout == 1'b0)
    );

endmodule