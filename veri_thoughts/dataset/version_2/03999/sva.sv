module sky130_fd_sc_ls__nor2_1_sva (
    input logic A,
    input logic B,
    input logic Y
);

    // Y must always equal the NOR of A and B.
    check_nor_function: assert property (
        @($global_clock) (Y === ~(A | B))
    );

    // When both inputs are low, Y must be high.
    check_y_high_for_00: assert property (
        @($global_clock) ((A === 1'b0) && (B === 1'b0)) |-> (Y === 1'b1)
    );

    // When A is high, Y must be low.
    check_y_low_for_a_high: assert property (
        @($global_clock) (A === 1'b1) |-> (Y === 1'b0)
    );

    // When B is high, Y must be low.
    check_y_low_for_b_high: assert property (
        @($global_clock) (B === 1'b1) |-> (Y === 1'b0)
    );

    // A high output implies both inputs are low.
    check_y_high_implies_inputs_low: assert property (
        @($global_clock) (Y === 1'b1) |-> ((A === 1'b0) && (B === 1'b0))
    );

    // A low output implies at least one input is high.
    check_y_low_implies_some_input_high: assert property (
        @($global_clock) (Y === 1'b0) |-> ((A === 1'b1) || (B === 1'b1))
    );

endmodule