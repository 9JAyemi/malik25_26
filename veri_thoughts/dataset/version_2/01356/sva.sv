module three_input_and_sva (
    input logic CLK,   // External verification clock (DUT has no clock/reset)
    input logic VPWR,
    input logic VGND,
    input logic a,
    input logic b,
    input logic c,
    input logic out
);
    // DUT is purely combinational 3-input NAND: out = ~(a & b & c); VPWR/VGND are unused by logic.

    // Output equals NAND of a, b, c.
    check_nand_function: assert property (
        @(posedge CLK) out == ~(a & b & c)
    );

    // DeMorgan equivalent form holds.
    check_demorgan_equivalence: assert property (
        @(posedge CLK) out == (~a | ~b | ~c)
    );

    // All inputs HIGH drives out LOW.
    check_all_high_out_low: assert property (
        @(posedge CLK) (a && b && c) |-> (out == 1'b0)
    );

    // Any input LOW drives out HIGH.
    check_any_low_out_high: assert property (
        @(posedge CLK) ((!a) || (!b) || (!c)) |-> (out == 1'b1)
    );

    // a LOW alone forces out HIGH.
    check_a_zero_forces_one: assert property (
        @(posedge CLK) (!a) |-> (out == 1'b1)
    );

    // b LOW alone forces out HIGH.
    check_b_zero_forces_one: assert property (
        @(posedge CLK) (!b) |-> (out == 1'b1)
    );

    // c LOW alone forces out HIGH.
    check_c_zero_forces_one: assert property (
        @(posedge CLK) (!c) |-> (out == 1'b1)
    );

    // With b and c HIGH, out equals ~a.
    check_bc_high_out_is_not_a: assert property (
        @(posedge CLK) (b && c) |-> (out == ~a)
    );

    // With a and c HIGH, out equals ~b.
    check_ac_high_out_is_not_b: assert property (
        @(posedge CLK) (a && c) |-> (out == ~b)
    );

    // With a and b HIGH, out equals ~c.
    check_ab_high_out_is_not_c: assert property (
        @(posedge CLK) (a && b) |-> (out == ~c)
    );

endmodule