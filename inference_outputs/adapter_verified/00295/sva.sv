module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [2:0] opcode,
    input logic [3:0] out,
    input logic zero
);

// No RTL reset; assertions are always active.

    // out equals A | B.
    check_out_is_or: assert property (
        @(posedge clk) out == (A | B)
    );

// zero equals (out == 4'h0).
    check_zero_matches_out_zero: assert property (
        @(posedge clk) zero == (out == 4'h0)
    );

// When opcode==000, out equals A+B (4-bit wrap).
    check_add_result: assert property (
        @(posedge clk) (opcode == 3'b000) |-> (out == (A + B))
    );

// When opcode==001, out equals A-B (4-bit wrap).
    check_sub_result: assert property (
        @(posedge clk) (opcode == 3'b001) |-> (out == (A - B))
    );

// When opcode==010, out equals A & B.
    check_and_result: assert property (
        @(posedge clk) (opcode == 3'b010) |-> (out == (A & B))
    );

// When opcode==011, out equals A | B.
    check_or_result: assert property (
        @(posedge clk) (opcode == 3'b011) |-> (out == (A | B))
    );

// When opcode==100, out equals A ^ B.
    check_xor_result: assert property (
        @(posedge clk) (opcode == 3'b100) |-> (out == (A ^ B))
    );

// For all opcodes not 000/001/010/011/100, out is zero.
    check_default_zero: assert property (
        @(posedge clk) (opcode != 3'b000 && opcode != 3'b001 && opcode != 3'b010 && opcode != 3'b011 && opcode != 3'b100) |-> (out == 4'h0)
    );

// If out is zero, zero must be asserted.
    check_zero_high_implies_out_zero: assert property (
        @(posedge clk) zero |-> (out == 4'h0)
    );

// If out is non-zero, zero must be deasserted.
    check_zero_low_implies_out_nonzero: assert property (
        @(posedge clk) !zero |-> (out != 4'h0)
    );

endmodule
