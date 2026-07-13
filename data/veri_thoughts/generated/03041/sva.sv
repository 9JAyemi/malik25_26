module shift_addsub_sva (
    input logic clk,
    input logic reset,
    input logic SER,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic sub,
    input logic [3:0] result,
    input logic [3:0] Q,
    input logic [3:0] shifted_Q,
    input logic [3:0] added_A,
    input logic [3:0] subbed_A
);

    // Reset clears the Q register.
    check_reset_clears_q: assert property (
        @(posedge clk) reset |-> (Q == 4'h0)
    );

    // Reset clears the shift register output.
    check_reset_clears_shifted_q: assert property (
        @(posedge clk) reset |-> (shifted_Q == 4'h0)
    );

    // The subtraction path computes shifted_Q minus A.
    check_subbed_a_difference: assert property (
        @(posedge clk) disable iff (reset)
        subbed_A == (shifted_Q - A)
    );

    // The add/sub output selects subtraction or addition based on sub.
    check_added_a_select: assert property (
        @(posedge clk) disable iff (reset)
        added_A == (sub ? subbed_A : (A + shifted_Q))
    );

    // The top-level result mux selects subbed_A or added_A.
    check_result_mux: assert property (
        @(posedge clk) disable iff (reset)
        result == (sub ? subbed_A : added_A)
    );

    // In subtract mode, result is shifted_Q minus A.
    check_result_sub_mode: assert property (
        @(posedge clk) disable iff (reset)
        sub |-> (result == (shifted_Q - A))
    );

    // In add mode, result is A plus shifted_Q.
    check_result_add_mode: assert property (
        @(posedge clk) disable iff (reset)
        !sub |-> (result == (A + shifted_Q))
    );

    // During reset, the subtraction path reduces to 0 minus A.
    check_reset_subbed_a_value: assert property (
        @(posedge clk) reset |-> (subbed_A == (4'h0 - A))
    );

    // During reset, result uses a zero shifted input.
    check_reset_result_value: assert property (
        @(posedge clk) reset |-> (result == (sub ? (4'h0 - A) : A))
    );

    // The top-level B input does not affect the datapath outputs.
    check_b_unused: assert property (
        @(posedge clk) disable iff (reset)
        ($changed(B) && $stable({A, sub, shifted_Q})) |-> $stable({subbed_A, added_A, result})
    );

    // SER does not affect the datapath outputs in this implementation.
    check_ser_unused: assert property (
        @(posedge clk) disable iff (reset)
        ($changed(SER) && $stable({A, sub, shifted_Q})) |-> $stable({subbed_A, added_A, result})
    );

endmodule