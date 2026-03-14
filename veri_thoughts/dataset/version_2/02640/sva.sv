module priority_encoder_4to2_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic x,
    input logic y
);
    // When a is high, output is 00 regardless of others.
    check_a_selects_00: assert property (
        @(posedge CLK) a |-> (x == 1'b0) && (y == 1'b0)
    );

    // When a is low and b is high, output is 10.
    check_b_selects_10: assert property (
        @(posedge CLK) (!a && b) |-> (x == 1'b1) && (y == 1'b0)
    );

    // When a and b are low and c is high, output is 01.
    check_c_selects_01: assert property (
        @(posedge CLK) (!a && !b && c) |-> (x == 1'b0) && (y == 1'b1)
    );

    // When a,b,c are low and d is high, output is 11.
    check_d_selects_11: assert property (
        @(posedge CLK) (!a && !b && !c && d) |-> (x == 1'b1) && (y == 1'b1)
    );

    // When all inputs are low, output is 00.
    check_none_selects_00: assert property (
        @(posedge CLK) (!a && !b && !c && !d) |-> (x == 1'b0) && (y == 1'b0)
    );

    // b has priority over c when a is low.
    check_b_overrides_c: assert property (
        @(posedge CLK) (!a && b && c) |-> (x == 1'b1) && (y == 1'b0)
    );

    // c has priority over d when a and b are low.
    check_c_overrides_d: assert property (
        @(posedge CLK) (!a && !b && c && d) |-> (x == 1'b0) && (y == 1'b1)
    );

    // x matches the RTL's LSB mapping.
    check_x_functional_equiv: assert property (
        @(posedge CLK) x == (a ? 1'b0 : b ? 1'b1 : c ? 1'b0 : d ? 1'b1 : 1'b0)
    );

    // y matches the RTL's mapping.
    check_y_functional_equiv: assert property (
        @(posedge CLK) y == (a ? 1'b0 : b ? 1'b0 : c ? 1'b1 : d ? 1'b1 : 1'b0)
    );

    // If y is 1, either c is selected or d is selected with higher-priority inputs low.
    check_y_one_implies_c_or_d: assert property (
        @(posedge CLK) y |-> ((!a && !b && c) || (!a && !b && !c && d))
    );
endmodule