module logic_module_sva (
    input logic a,
    input logic b,
    input logic g_out,
    input logic p_out
);
    // No clock or reset in RTL; combinational logic. Assertions sample on a/b edges.

    // g_out implements logical AND of a and b.
    check_g_out_and_def: assert property (
        @(posedge a or negedge a or posedge b or negedge b) g_out == (a & b)
    );

    // p_out implements XOR of a and b (since xnor(b, ~a) == a ^ b).
    check_p_out_xor_def: assert property (
        @(posedge a or negedge a or posedge b or negedge b) p_out == (a ^ b)
    );

    // If g_out is HIGH, both inputs must be HIGH.
    check_g_out_high_requires_inputs_high: assert property (
        @(posedge a or negedge a or posedge b or negedge b) g_out |-> (a && b)
    );

    // When inputs differ, p_out must be 1.
    check_p_out_one_when_inputs_differ: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (a ^ b) |-> (p_out == 1'b1)
    );

    // When inputs are equal, p_out must be 0.
    check_p_out_zero_when_inputs_equal: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (!(a ^ b)) |-> (p_out == 1'b0)
    );

    // If any input is 0, g_out must be 0.
    check_g_out_zero_if_any_input_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) ((!a) || (!b)) |-> (g_out == 1'b0)
    );

    // g_out and p_out can never be HIGH simultaneously.
    check_grant_mutex_gp_high: assert property (
        @(posedge a or negedge a or posedge b or negedge b) !(g_out && p_out)
    );

    // If a is 0, p_out must equal b.
    check_p_out_when_a_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (!a) |-> (p_out == b)
    );

    // If a is 1, p_out must equal ~b.
    check_p_out_when_a_one: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (a) |-> (p_out == ~b)
    );

    // If b is 1, g_out must equal a.
    check_g_out_equals_a_when_b_one: assert property (
        @(posedge a or negedge a or posedge b or negedge b) b |-> (g_out == a)
    );
endmodule