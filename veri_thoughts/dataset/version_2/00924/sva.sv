module and_gate_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic out,
    input logic temp1,
    input logic temp2,
    input logic temp3
);
    ///// Gate-level structure checks /////
    // gate1: temp1 is NAND of a and b.
    check_gate1_is_nand: assert property (
        @(posedge clk) disable iff (1'b0) temp1 == ~(a & b)
    );
    // gate2: temp2 is NAND of temp1 and c.
    check_gate2_is_nand: assert property (
        @(posedge clk) disable iff (1'b0) temp2 == ~(temp1 & c)
    );
    // gate3: temp3 is NAND of temp2 and d.
    check_gate3_is_nand: assert property (
        @(posedge clk) disable iff (1'b0) temp3 == ~(temp2 & d)
    );
    // gate4: out is inversion of temp3 (NAND of a signal with itself).
    check_gate4_is_inv: assert property (
        @(posedge clk) disable iff (1'b0) out == ~temp3
    );

    ///// Functional equivalence /////
    // out equals d & ((a & b) | ~c).
    check_function_equivalence: assert property (
        @(posedge clk) disable iff (1'b0) out == (d & ((a & b) | ~c))
    );

    ///// Useful implications derived from the logic /////
    // If d is LOW then out must be LOW.
    check_d_low_forces_out_low: assert property (
        @(posedge clk) disable iff (1'b0) (d == 1'b0) |-> (out == 1'b0)
    );
    // If c is LOW then out equals d.
    check_c_low_passes_d: assert property (
        @(posedge clk) disable iff (1'b0) (c == 1'b0) |-> (out == d)
    );
    // If a and b are both HIGH then out equals d.
    check_ab_high_passes_d: assert property (
        @(posedge clk) disable iff (1'b0) (a && b) |-> (out == d)
    );
    // If c is HIGH and (a & b) is LOW then out is LOW.
    check_c_high_and_ab_low_out_low: assert property (
        @(posedge clk) disable iff (1'b0) (c && !(a && b)) |-> (out == 1'b0)
    );
    // If c and d are HIGH then out equals a & b.
    check_cd_high_out_equals_ab: assert property (
        @(posedge clk) disable iff (1'b0) (c && d) |-> (out == (a & b))
    );
endmodule