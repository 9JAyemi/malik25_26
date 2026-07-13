module fadder_sva #(parameter WIDTH = 8) (
    input logic clk,
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic sub_enable,
    input logic carry_in,
    input logic [WIDTH-1:0] res,
    input logic carry_out
);

    // Add mode matches a + b + carry_in.
    check_add_mode_full_sum: assert property (
        @(posedge clk)
        !sub_enable |-> ({carry_out, res} == ({1'b0, a} + {1'b0, b} + carry_in))
    );

    // Invert-b mode matches a + ~b + carry_in.
    check_invert_b_mode_full_sum: assert property (
        @(posedge clk)
        sub_enable |-> ({carry_out, res} == ({1'b0, a} + {1'b0, ~b} + carry_in))
    );

    // The LSB sum bit follows the full-adder XOR equation.
    check_lsb_sum_bit: assert property (
        @(posedge clk)
        res[0] == (a[0] ^ (sub_enable ? ~b[0] : b[0]) ^ carry_in)
    );

    // Zero b with no carry passes a through in add mode.
    check_add_zero_b_identity: assert property (
        @(posedge clk)
        !sub_enable && (b == {WIDTH{1'b0}}) && !carry_in |-> ((res == a) && (carry_out == 1'b0))
    );

    // Zero a with no carry passes b through in add mode.
    check_add_zero_a_identity: assert property (
        @(posedge clk)
        !sub_enable && (a == {WIDTH{1'b0}}) && !carry_in |-> ((res == b) && (carry_out == 1'b0))
    );

    // All-ones b plus carry wraps and leaves a in add mode.
    check_add_all_ones_b_wrap: assert property (
        @(posedge clk)
        !sub_enable && (b == {WIDTH{1'b1}}) && carry_in |-> ((res == a) && (carry_out == 1'b1))
    );

    // Equal operands cancel in invert-b mode when carry_in is high.
    check_invert_b_equal_operands_with_carry_cancel: assert property (
        @(posedge clk)
        sub_enable && carry_in && (a == b) |-> ((res == {WIDTH{1'b0}}) && (carry_out == 1'b1))
    );

    // Equal operands produce all ones in invert-b mode when carry_in is low.
    check_invert_b_equal_operands_without_carry_all_ones: assert property (
        @(posedge clk)
        sub_enable && !carry_in && (a == b) |-> ((res == {WIDTH{1'b1}}) && (carry_out == 1'b0))
    );

    // Zero b with carry_in high leaves a unchanged in invert-b mode.
    check_invert_b_zero_b_with_carry_identity: assert property (
        @(posedge clk)
        sub_enable && (b == {WIDTH{1'b0}}) && carry_in |-> ((res == a) && (carry_out == 1'b1))
    );

    // All-ones b with no carry leaves a unchanged in invert-b mode.
    check_invert_b_all_ones_b_without_carry_identity: assert property (
        @(posedge clk)
        sub_enable && (b == {WIDTH{1'b1}}) && !carry_in |-> ((res == a) && (carry_out == 1'b0))
    );

    generate
        if (WIDTH == 1) begin : g_width1
            // For WIDTH=1, carry_out follows the single-bit carry equation.
            check_single_bit_carry_formula: assert property (
                @(posedge clk)
                carry_out == (((a[0] ^ (sub_enable ? ~b[0] : b[0])) & carry_in) |
                              (a[0] & (sub_enable ? ~b[0] : b[0])))
            );
        end
    endgenerate

endmodule