module calculator_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [1:0] op,
    input logic [7:0] result
);
    // No explicit clock/reset; combinational DUT; sample assertions on posedge of op[0].

    // When op==00, result equals a + b (8-bit wrap).
    check_add_result: assert property (
        @(posedge op[0]) (op == 2'b00) |-> (result == (a + b))
    );

    // When op==01, result equals a - b (8-bit wrap).
    check_sub_result: assert property (
        @(posedge op[0]) (op == 2'b01) |-> (result == (a - b))
    );

    // When op==10, result equals low 8 bits of a * b.
    check_mul_result: assert property (
        @(posedge op[0]) (op == 2'b10) |-> (result == (a * b)[7:0])
    );

    // When op==11 and b!=0, result equals a / b.
    check_div_result_nonzero: assert property (
        @(posedge op[0]) ((op == 2'b11) && (b != 8'd0)) |-> (result == (a / b))
    );

    // Result is stable if a, b, and op are unchanged.
    check_stable_when_inputs_stable: assert property (
        @(posedge op[0]) (a == $past(a) && b == $past(b) && op == $past(op)) |-> (result == $past(result))
    );
endmodule