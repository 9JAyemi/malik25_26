module bitwise_op_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] sel,
    input logic [3:0] out
);

    // When sel selects AND, out matches A & B.
    check_sel_and: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b00) |-> (out == (A & B))
    );

    // When sel selects OR, out matches A | B.
    check_sel_or: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b01) |-> (out == (A | B))
    );

    // When sel selects XOR, out matches A ^ B.
    check_sel_xor: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b10) |-> (out == (A ^ B))
    );

    // When sel selects XNOR, out matches ~(A ^ B).
    check_sel_xnor: assert property (
        @(posedge clk) disable iff (1'b0)
        (sel == 2'b11) |-> (out == ~(A ^ B))
    );

    // With stable inputs and select, the combinational output stays stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (1'b0)
        $stable({A, B, sel}) |-> $stable(out)
    );

endmodule