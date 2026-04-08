module my_module_sva (
    input logic clk,
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic X
);

    // X must match the complete combinational function.
    check_full_function: assert property (
        @(posedge clk) X == ((A1 ? A2 : (A3 ^ A4)) ^ B1)
    );

    // When A1 selects A2 and B1 is low, X matches A2.
    check_a2_selected_passthrough: assert property (
        @(posedge clk) (A1 && !B1) |-> (X == A2)
    );

    // When A1 selects A2 and B1 is high, X is the inverse of A2.
    check_a2_selected_inverted: assert property (
        @(posedge clk) (A1 && B1) |-> (X == ~A2)
    );

    // When A1 selects the XOR path and B1 is low, X matches A3 ^ A4.
    check_xor_selected_passthrough: assert property (
        @(posedge clk) (!A1 && !B1) |-> (X == (A3 ^ A4))
    );

    // When A1 selects the XOR path and B1 is high, X is the inverse of A3 ^ A4.
    check_xor_selected_inverted: assert property (
        @(posedge clk) (!A1 && B1) |-> (X == ~(A3 ^ A4))
    );

    // With B1 low, X passes the selected value unchanged.
    check_b1_low_passthrough: assert property (
        @(posedge clk) (!B1) |-> (X == (A1 ? A2 : (A3 ^ A4)))
    );

    // With B1 high, X is the inverse of the selected value.
    check_b1_high_inverts_selected_value: assert property (
        @(posedge clk) B1 |-> (X == ~((A1 ? A2 : (A3 ^ A4))))
    );

endmodule