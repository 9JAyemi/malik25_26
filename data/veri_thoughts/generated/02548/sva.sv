module nor_gate_sva (
    input logic a,
    input logic b,
    input logic out
);
    // Note: No clock/reset in RTL; combinational logic; sample on any edge of a or b.

    // Functional equivalence: out equals a OR b.
    check_out_is_or: assert property (
        @(posedge a or negedge a or posedge b or negedge b) out == (a | b)
    );

    // De Morgan form: out equals ~(~a & ~b).
    check_demorgan_equiv: assert property (
        @(posedge a or negedge a or posedge b or negedge b) out == ~(~a & ~b)
    );

    // When both inputs are 0, out must be 0.
    check_both_zero_out_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (!a && !b) |-> (out == 1'b0)
    );

    // When a is 1, out must be 1.
    check_a_high_out_high: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (a == 1'b1) |-> (out == 1'b1)
    );

    // When b is 1, out must be 1.
    check_b_high_out_high: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (b == 1'b1) |-> (out == 1'b1)
    );

    // If out is 0, both inputs must be 0.
    check_out_zero_implies_inputs_zero: assert property (
        @(posedge a or negedge a or posedge b or negedge b) (out == 1'b0) |-> (!a && !b)
    );

endmodule