module bitwise_xor_sva (
    input logic clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] result
);
    // Result equals bitwise XOR of inputs every cycle.
    check_result_matches_xor: assert property (
        @(posedge clk) result == (a ^ b)
    );

    // If inputs are equal, result is zero.
    check_zero_when_inputs_equal: assert property (
        @(posedge clk) (a == b) |-> (result == 8'h00)
    );

    // If b is zero, result equals a.
    check_passthrough_when_b_zero: assert property (
        @(posedge clk) (b == 8'h00) |-> (result == a)
    );

    // If a is zero, result equals b.
    check_passthrough_when_a_zero: assert property (
        @(posedge clk) (a == 8'h00) |-> (result == b)
    );

    // If b is bitwise-not of a, result is all ones.
    check_ones_when_b_is_not_a: assert property (
        @(posedge clk) (b == ~a) |-> (result == 8'hFF)
    );

    // If both inputs are stable, result is stable.
    check_stability_with_stable_inputs: assert property (
        @(posedge clk) $stable(a) && $stable(b) |-> $stable(result)
    );

    // When b is zero and stable, result tracks changes in a.
    check_result_tracks_a_when_b_zero: assert property (
        @(posedge clk) (b == 8'h00) && $stable(b) && $changed(a) |-> $changed(result) && (result == a)
    );

    // When a is zero and stable, result tracks changes in b.
    check_result_tracks_b_when_a_zero: assert property (
        @(posedge clk) (a == 8'h00) && $stable(a) && $changed(b) |-> $changed(result) && (result == b)
    );

    // When b is all ones, result is bitwise-not of a.
    check_result_inverts_a_when_b_ones: assert property (
        @(posedge clk) (b == 8'hFF) |-> (result == ~a)
    );

    // When a is all ones, result is bitwise-not of b.
    check_result_inverts_b_when_a_ones: assert property (
        @(posedge clk) (a == 8'hFF) |-> (result == ~b)
    );
endmodule