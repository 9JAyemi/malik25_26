module bitwise_op_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [2:0] op,
    input logic [7:0] out
);
    // For op=000, out must be a & b.
    check_map_and: assert property (
        @(posedge CLK) (op == 3'b000) |-> (out == (a & b))
    );

    // For op=001, out must be a | b.
    check_map_or: assert property (
        @(posedge CLK) (op == 3'b001) |-> (out == (a | b))
    );

    // For op=010, out must be a ^ b.
    check_map_xor: assert property (
        @(posedge CLK) (op == 3'b010) |-> (out == (a ^ b))
    );

    // For op=011, out must be two's complement of a (~a + 1).
    check_map_neg_a: assert property (
        @(posedge CLK) (op == 3'b011) |-> (out == (~a + 8'd1))
    );

    // For op=100, out must be two's complement of b (~b + 1).
    check_map_neg_b: assert property (
        @(posedge CLK) (op == 3'b100) |-> (out == (~b + 8'd1))
    );

    // For op=101, out must be ~(a & b) (bitwise NAND).
    check_map_nand: assert property (
        @(posedge CLK) (op == 3'b101) |-> (out == ~(a & b))
    );

    // For op=110, out must be ~(a | b) (bitwise NOR).
    check_map_nor: assert property (
        @(posedge CLK) (op == 3'b110) |-> (out == ~(a | b))
    );

    // For op=111, out must be ~(a ^ b) (bitwise XNOR).
    check_map_xnor: assert property (
        @(posedge CLK) (op == 3'b111) |-> (out == ~(a ^ b))
    );

    // If a, b, and op are stable, out must be stable (combinational behavior).
    check_stable_out_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(a) && $stable(b) && $stable(op)) |-> $stable(out)
    );

    // For op=011, a + out wraps to 0 (two's complement identity).
    check_neg_a_sum_zero: assert property (
        @(posedge CLK) (op == 3'b011) |-> ((a + out) == 8'h00)
    );

    // For op=100, b + out wraps to 0 (two's complement identity).
    check_neg_b_sum_zero: assert property (
        @(posedge CLK) (op == 3'b100) |-> ((b + out) == 8'h00)
    );
endmodule