module GrayCodeStateMachine_sva #(parameter n = 4) (
    input logic clk,
    input logic [n-1:0] state
);

    function automatic [n-1:0] gray_code(input [n-1:0] binary_code);
        begin
            gray_code = binary_code ^ (binary_code >> 1);
        end
    endfunction

    function automatic [n-1:0] gray_to_binary(input [n-1:0] gray_code_in);
        integer i;
        begin
            gray_to_binary[n-1] = gray_code_in[n-1];
            for (i = n-2; i >= 0; i = i - 1)
                gray_to_binary[i] = gray_to_binary[i+1] ^ gray_code_in[i];
        end
    endfunction

    // The initialized counter value produces a zero Gray state first.
    check_initial_state_zero: assert property (
        @(posedge clk) $initstate |-> (state == {n{1'b0}})
    );

    // The decoded count advances by one on each clock.
    check_binary_count_increments: assert property (
        @(posedge clk) !$initstate |-> (gray_to_binary(state) == (gray_to_binary($past(state)) + {{(n-1){1'b0}}, 1'b1}))
    );

    // The current state is the Gray code of the incremented prior count.
    check_gray_sequence_progression: assert property (
        @(posedge clk) !$initstate |-> (state == gray_code(gray_to_binary($past(state)) + {{(n-1){1'b0}}, 1'b1}))
    );

    // Consecutive Gray states differ by exactly one bit.
    check_single_bit_transition: assert property (
        @(posedge clk) !$initstate |-> $onehot(state ^ $past(state))
    );

    // An all-ones decoded count wraps back to zero Gray code.
    check_wrap_to_zero: assert property (
        @(posedge clk) !$initstate && (gray_to_binary($past(state)) == {n{1'b1}}) |-> (state == {n{1'b0}})
    );

    // A zero Gray state advances to the Gray code for binary one.
    check_zero_advances_to_one: assert property (
        @(posedge clk) !$initstate && ($past(state) == {n{1'b0}}) |-> (state == {{(n-1){1'b0}}, 1'b1})
    );

endmodule