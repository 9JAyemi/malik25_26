module four_input_one_output_sva (
    input logic CLK,
    input logic a,
    input logic b,
    input logic c,
    input logic d,
    input logic x
);
    // x equals the combinational function of inputs
    check_functional_equivalence: assert property (
        @(posedge CLK) x == (a || ((!a) && (!b) && ((!c) || d)))
    );

    // If a is 1 then x must be 1
    check_a_implies_x: assert property (
        @(posedge CLK) a |-> x
    );

    // If a is 0 and b is 1 then x must be 0
    check_not_a_and_b_implies_not_x: assert property (
        @(posedge CLK) (!a && b) |-> (!x)
    );

    // If a=0,b=0,c=0 then x must be 1
    check_not_a_not_b_not_c_implies_x: assert property (
        @(posedge CLK) (!a && !b && !c) |-> x
    );

    // If a=0,b=0,c=1,d=1 then x must be 1
    check_not_a_not_b_c_d_implies_x: assert property (
        @(posedge CLK) (!a && !b && c && d) |-> x
    );

    // If a=0,b=0,c=1,d=0 then x must be 0
    check_not_a_not_b_c_and_not_d_implies_not_x: assert property (
        @(posedge CLK) (!a && !b && c && !d) |-> (!x)
    );

    // When a=0 and b=0, x equals (!c || d)
    check_not_a_not_b_equation: assert property (
        @(posedge CLK) (!a && !b) |-> (x == ((!c) || d))
    );

    // If x is 1 while a is 0, then b must be 0 and (!c || d) must hold
    check_x_and_not_a_implies_conditions: assert property (
        @(posedge CLK) (x && !a) |-> (!b && ((!c) || d))
    );

    // If x is 0, then a must be 0 and (b || (c && !d)) must hold
    check_not_x_implies_conditions: assert property (
        @(posedge CLK) (!x) |-> (!a && (b || (c && !d)))
    );

    // When b is 1, x equals a
    check_b_one_implies_x_eq_a: assert property (
        @(posedge CLK) b |-> (x == a)
    );

    // When b=0 and c=0, x must be 1
    check_b_zero_c_zero_implies_x_one: assert property (
        @(posedge CLK) (!b && !c) |-> x
    );
endmodule