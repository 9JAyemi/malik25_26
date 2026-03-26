module address_operation_assertions (
    input logic [8:0] address_a,
    input logic [8:0] address_b,
    input logic       clock,
    input logic [3:0] q_a,
    input logic [3:0] q_b
);

    // q_a reflects the prior-cycle address_a computation.
    check_q_a_function: assert property (
        @(posedge clock)
        1'b1 |=> (q_a == ($past(address_a[8]) ? ($past(address_a[3:0]) + 4'd1)
                                              : ($past(address_a[3:0]) + 4'd2)))
    );

    // q_b reflects the prior-cycle address_b computation.
    check_q_b_function: assert property (
        @(posedge clock)
        1'b1 |=> (q_b == ($past(address_b[8]) ? ($past(address_b[3:0]) + 4'd1)
                                              : ($past(address_b[3:0]) + 4'd2)))
    );

    // q_a stays unchanged when its controlling address bits stay unchanged.
    check_q_a_stable_when_relevant_bits_stable: assert property (
        @(posedge clock)
        ((address_a[8] == $past(address_a[8])) &&
         (address_a[3:0] == $past(address_a[3:0])))
        |=> (q_a == $past(q_a))
    );

    // q_b stays unchanged when its controlling address bits stay unchanged.
    check_q_b_stable_when_relevant_bits_stable: assert property (
        @(posedge clock)
        ((address_b[8] == $past(address_b[8])) &&
         (address_b[3:0] == $past(address_b[3:0])))
        |=> (q_b == $past(q_b))
    );

    // Matching relevant bits on both inputs produce matching outputs.
    check_matching_inputs_produce_matching_outputs: assert property (
        @(posedge clock)
        ((address_a[8] == address_b[8]) &&
         (address_a[3:0] == address_b[3:0]))
        |=> (q_a == q_b)
    );

endmodule