module top_module_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic d,
    input logic [3:0] out_nand_bitwise,
    input logic out_nand_logical,
    input logic [3:0] out_xor_bitwise,
    input logic out_xor_logical,
    input logic q
);

    // Bitwise NAND output matches ~(a & b).
    check_out_nand_bitwise_function: assert property (
        @(posedge clk) out_nand_bitwise == ~(a & b)
    );

    // Logical NAND output is high only when a & b is zero.
    check_out_nand_logical_function: assert property (
        @(posedge clk) out_nand_logical == ((a & b) == 4'b0000)
    );

    // Bitwise XOR output matches a ^ b.
    check_out_xor_bitwise_function: assert property (
        @(posedge clk) out_xor_bitwise == (a ^ b)
    );

    // Logical XOR output is high only when a equals b.
    check_out_xor_logical_function: assert property (
        @(posedge clk) out_xor_logical == (a == b)
    );

    // NAND logical output matches an all-ones bitwise NAND result.
    check_nand_outputs_consistent: assert property (
        @(posedge clk) out_nand_logical == (out_nand_bitwise == 4'b1111)
    );

    // XOR logical output matches an all-zeros bitwise XOR result.
    check_xor_outputs_consistent: assert property (
        @(posedge clk) out_xor_logical == (out_xor_bitwise == 4'b0000)
    );

    // q can only be high when the logical NAND output is high.
    check_q_requires_nand_logical: assert property (
        @(posedge clk) q |-> out_nand_logical
    );

    // Four consecutive d highs make q match out_nand_logical on the next cycle.
    check_four_high_ds_set_q_from_nand_logical: assert property (
        @(posedge clk) (d ##1 d ##1 d ##1 d) |=> (q == out_nand_logical)
    );

    // Four consecutive d lows force q low on the next cycle.
    check_four_low_ds_clear_q: assert property (
        @(posedge clk) ((!d) ##1 (!d) ##1 (!d) ##1 (!d)) |=> !q
    );

endmodule