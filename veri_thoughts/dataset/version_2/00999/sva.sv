module simple_arithmetic_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [1:0] op,
    input logic [7:0] out
);
    ///// Functional mapping /////
    // Out matches the RTL ternary selection of operations.
    check_functional_equivalence: assert property (
        @(posedge clk) out == ((op == 2'b00) ? (A + B) :
                               (op == 2'b01) ? (A - B) :
                               (op == 2'b10) ? (A & B) :
                                               (A | B))
    );

    ///// Operation selections /////
    // When op==00, out equals A+B (8-bit wraparound).
    check_add_selection: assert property (
        @(posedge clk) (op === 2'b00) |-> (out == (A + B))
    );

    // When op==01, out equals A-B (8-bit wraparound).
    check_sub_selection: assert property (
        @(posedge clk) (op === 2'b01) |-> (out == (A - B))
    );

    // When op==10, out equals A&B.
    check_and_selection: assert property (
        @(posedge clk) (op === 2'b10) |-> (out == (A & B))
    );

    // When op==11, out equals A|B.
    check_or_selection: assert property (
        @(posedge clk) (op === 2'b11) |-> (out == (A | B))
    );

    // For any op not 00/01/10 (including X/Z), out falls through to OR.
    check_default_fallthrough_to_or: assert property (
        @(posedge clk) ((op !== 2'b00) && (op !== 2'b01) && (op !== 2'b10)) |-> (out == (A | B))
    );

    ///// Stability /////
    // With stable inputs and op across a cycle, out remains stable.
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(op) |-> $stable(out)
    );
endmodule