module two_input_logic_sva (
    input logic a,
    input logic b,
    input logic op,
    input logic out
);

    // No RTL clock or reset is present; sample on Jasper's global clock.
    // Output must always match the implemented combinational expression.
    check_out_matches_rtl_expression: assert property (
        @($global_clock) out == (op ? ~a : (a ^ b))
    );

    // When op is high, out must be the inversion of a.
    check_out_invert_a_when_op_high: assert property (
        @($global_clock) op |-> (out == ~a)
    );

    // When op is low, out must be the XOR of a and b.
    check_out_xor_when_op_low: assert property (
        @($global_clock) !op |-> (out == (a ^ b))
    );

endmodule