module bitwise_op_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] sel,
    input logic [3:0] out
);

// sel=00 selects bitwise AND.
    check_and_select: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == (A & B))
    );

// sel=01 selects bitwise OR.
    check_or_select: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == (A | B))
    );

// sel=10 selects bitwise XOR.
    check_xor_select: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == (A ^ B))
    );

// sel=11 selects bitwise XNOR.
    check_xnor_select: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == ~(A ^ B))
    );

// Output always matches the selected operation.
    check_selected_operation: assert property (
        @(posedge clk)
        (sel == 2'b00) || (sel == 2'b01) || (sel == 2'b10) || (sel == 2'b11)
        |-> (out == ((sel == 2'b00) ? (A & B) :
                      (sel == 2'b01) ? (A | B) :
                      (sel == 2'b10) ? (A ^ B) :
                                        ~(A ^ B)))
    );

// When A equals B, XOR and XNOR select the same result.
    check_xor_xnor_equal_when_equal: assert property (
        @(posedge clk) (A == B) |-> ((out == (A ^ B)) == (out == ~(A ^ B)))
    );

// When A equals B, OR equals AND.
    check_or_and_equal_when_equal: assert property (
        @(posedge clk) (A == B) |-> ((out == (A | B)) == (out == (A & B)))
    );

// When A equals B, output equals A (and B).
    check_equal_inputs_pass_through: assert property (
        @(posedge clk) (A == B) |-> (out == A)
    );

endmodule
