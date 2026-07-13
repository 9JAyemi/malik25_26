module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);
    // Output matches the 2:1 mux equation.
    check_mux_equation: assert property (
        @(posedge a or posedge b or posedge sel_b1 or posedge sel_b2)
        out_always == ((sel_b2 & ~sel_b1) ? b : a)
    );

    // When sel_b2=1 and sel_b1=0, output equals b.
    check_b_selected: assert property (
        @(posedge a or posedge b or posedge sel_b1 or posedge sel_b2)
        (sel_b2 && !sel_b1) |-> (out_always == b)
    );

    // When sel_b2=0, output equals a.
    check_a_when_sel_b2_low: assert property (
        @(posedge a or posedge b or posedge sel_b1 or posedge sel_b2)
        (!sel_b2) |-> (out_always == a)
    );

    // When sel_b1=1, output equals a.
    check_a_when_sel_b1_high: assert property (
        @(posedge a or posedge b or posedge sel_b1 or posedge sel_b2)
        (sel_b1) |-> (out_always == a)
    );

    // If a and b are equal, output equals that value.
    check_equal_inputs_pass_through: assert property (
        @(posedge a or posedge b or posedge sel_b1 or posedge sel_b2)
        (a == b) |-> (out_always == a)
    );
endmodule