module top_module_sva (
    input  logic        clk,
    input  logic        reset,                 // synchronous active-high reset
    input  logic [3:0]  a,
    input  logic [3:0]  b,
    input  logic [3:0]  gray_product,
    // Internal signals from top_module
    input  logic [7:0]  binary_product,
    input  logic [7:0]  binary_product_reg,
    input  logic [3:0]  gray_a,
    input  logic [3:0]  gray_b
);
    ///// Reset behavior /////
    // On a reset cycle, next-cycle registered outputs must be zero.
    reset_clears_regs: assert property (
        @(posedge clk) reset |=> (binary_product_reg == 8'b0) && (gray_product == 4'b0)
    );

    // First cycle after leaving reset, registered outputs remain zero.
    post_reset_regs_zero: assert property (
        @(posedge clk) ($past(reset) && !reset) |-> (binary_product_reg == 8'b0) && (gray_product == 4'b0)
    );

    ///// Combinational block correctness /////
    // gray_a is combinational Gray code of a.
    check_gray_a_comb: assert property (
        @(posedge clk) disable iff (reset) gray_a == (a ^ (a >> 1))
    );

    // gray_b is combinational Gray code of b.
    check_gray_b_comb: assert property (
        @(posedge clk) disable iff (reset) gray_b == (b ^ (b >> 1))
    );

    // binary_product is combinational multiplication a*b.
    check_comb_multiplier: assert property (
        @(posedge clk) disable iff (reset) binary_product == (a * b)
    );

    // If either operand is zero, combinational product is zero.
    check_mult_by_zero: assert property (
        @(posedge clk) disable iff (reset) ((a == 4'b0) || (b == 4'b0)) |-> (binary_product == 8'b0)
    );

    ///// Sequential register updates /////
    // binary_product_reg captures binary_product on the next cycle (when not preceded by reset).
    check_bin_reg_tracks_wire: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (binary_product_reg == $past(binary_product))
    );

    // binary_product_reg equals previous-cycle a*b (when not preceded by reset).
    check_bin_reg_eq_past_mult: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (binary_product_reg == $past(a * b))
    );

    // gray_product captures gray_a ^ gray_b from the previous cycle (when not preceded by reset).
    check_gray_product_prev_grayxor: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (gray_product == $past(gray_a ^ gray_b))
    );

    // gray_product equals previous-cycle (gray(a) ^ gray(b)) computed from a,b (when not preceded by reset).
    check_gray_product_prev_func: assert property (
        @(posedge clk) disable iff (reset) (!$past(reset)) |-> (gray_product == $past((a ^ (a >> 1)) ^ (b ^ (b >> 1))))
    );

endmodule