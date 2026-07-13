module three_input_op_sva (
    input logic Y,
    input logic A,
    input logic B,
    input logic C,
    input logic [1:0] op,
    input logic sel,
    input logic [2:0] input_signals,
    input logic [1:0] selected_signals,
    input logic [2:0] and_results,
    input logic [2:0] or_results,
    input logic [2:0] xor_results,
    input logic [2:0] xnor_results
);

    // sel=0 drives input_signals[0]=A, [1]=B, [2]=B.
    check_input_map_sel0: assert property (
        @($global_clock) (sel == 1'b0) |-> (input_signals == {B, B, A})
    );

    // sel=1 drives input_signals[0]=B, [1]=B, [2]=C.
    check_input_map_sel1: assert property (
        @($global_clock) (sel == 1'b1) |-> (input_signals == {C, B, B})
    );

    // sel=0 selects result index 0.
    check_selected_signals_sel0: assert property (
        @($global_clock) (sel == 1'b0) |-> (selected_signals == 2'b00)
    );

    // sel=1 selects result index 2.
    check_selected_signals_sel1: assert property (
        @($global_clock) (sel == 1'b1) |-> (selected_signals == 2'b10)
    );

    // and_results holds the three pairwise AND terms.
    check_and_results: assert property (
        @($global_clock)
        (and_results == {
            (input_signals[2] & input_signals[0]),
            (input_signals[1] & input_signals[2]),
            (input_signals[0] & input_signals[1])
        })
    );

    // or_results holds the three pairwise OR terms.
    check_or_results: assert property (
        @($global_clock)
        (or_results == {
            (input_signals[2] | input_signals[0]),
            (input_signals[1] | input_signals[2]),
            (input_signals[0] | input_signals[1])
        })
    );

    // xor_results holds the three pairwise XOR terms.
    check_xor_results: assert property (
        @($global_clock)
        (xor_results == {
            (input_signals[2] ^ input_signals[0]),
            (input_signals[1] ^ input_signals[2]),
            (input_signals[0] ^ input_signals[1])
        })
    );

    // xnor_results holds the three pairwise XNOR terms.
    check_xnor_results: assert property (
        @($global_clock)
        (xnor_results == {
            ~(input_signals[2] ^ input_signals[0]),
            ~(input_signals[1] ^ input_signals[2]),
            ~(input_signals[0] ^ input_signals[1])
        })
    );

    // op=00 drives Y from the selected AND result.
    check_output_and: assert property (
        @($global_clock) (op == 2'b00) |-> (Y == and_results[selected_signals])
    );

    // op=01 drives Y from the selected OR result.
    check_output_or: assert property (
        @($global_clock) (op == 2'b01) |-> (Y == or_results[selected_signals])
    );

    // op=10 drives Y from the selected XOR result.
    check_output_xor: assert property (
        @($global_clock) (op == 2'b10) |-> (Y == xor_results[selected_signals])
    );

    // op=11 drives Y from the selected XNOR result.
    check_output_xnor: assert property (
        @($global_clock) (op == 2'b11) |-> (Y == xnor_results[selected_signals])
    );

endmodule