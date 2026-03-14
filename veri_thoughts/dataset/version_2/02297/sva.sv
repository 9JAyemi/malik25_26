module nor4_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic y,
    input logic ab, // internal net in nor4
    input logic cd  // internal net in nor4
);
    // ab must be NOR of a and b
    check_ab_is_nor2: assert property (
        @(posedge CLK) ab == ~(a | b)
    );

    // cd must be NOR of c and d
    check_cd_is_nor2: assert property (
        @(posedge CLK) cd == ~(c | d)
    );

    // y must be NOR of ab and cd
    check_y_is_nor2_of_ab_cd: assert property (
        @(posedge CLK) y == ~(ab | cd)
    );

    // y must equal (a|b)&(c|d)
    check_y_equals_and_of_ors: assert property (
        @(posedge CLK) y == ((a | b) & (c | d))
    );

    // If a and b are both 0, y must be 0
    check_y_zero_if_a_b_both_zero: assert property (
        @(posedge CLK) (!a && !b) |-> (y == 1'b0)
    );

    // If c and d are both 0, y must be 0
    check_y_zero_if_c_d_both_zero: assert property (
        @(posedge CLK) (!c && !d) |-> (y == 1'b0)
    );

    // If at least one of a/b and one of c/d are 1, y must be 1
    check_y_one_if_each_pair_has_one: assert property (
        @(posedge CLK) (((a | b) & (c | d)) == 1'b1) |-> (y == 1'b1)
    );

    // If y is 1 then ab and cd must both be 0
    check_y_high_implies_ab_cd_low: assert property (
        @(posedge CLK) (y == 1'b1) |-> ((ab == 1'b0) && (cd == 1'b0))
    );

    // If y is 0 then either ab or cd must be 1
    check_y_low_implies_ab_or_cd_high: assert property (
        @(posedge CLK) (y == 1'b0) |-> ((ab == 1'b1) || (cd == 1'b1))
    );

    // y can change only if at least one input changes
    check_y_changes_only_with_inputs: assert property (
        @(posedge CLK) $changed(y) |-> $changed({a,b,c,d})
    );
endmodule