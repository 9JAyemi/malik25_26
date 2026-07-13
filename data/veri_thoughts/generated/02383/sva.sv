module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

    // When sel_b2:sel_b1 == 2'b00, output must equal b.
    check_case_00_selects_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ({sel_b2, sel_b1} == 2'b00) |=> (out_always == b)
    );

    // When sel_b2:sel_b1 == 2'b01, output must equal a.
    check_case_01_selects_a: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ({sel_b2, sel_b1} == 2'b01) |=> (out_always == a)
    );

    // When sel_b2:sel_b1 == 2'b10, output must equal b.
    check_case_10_selects_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ({sel_b2, sel_b1} == 2'b10) |=> (out_always == b)
    );

    // When sel_b2:sel_b1 == 2'b11, output must equal b.
    check_case_11_selects_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        ({sel_b2, sel_b1} == 2'b11) |=> (out_always == b)
    );

    // Functional equivalence to truth table: out = (sel_b2==0 && sel_b1==1) ? a : b.
    check_mux_function_equiv: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        (out_always == ((~sel_b2 & sel_b1) ? a : b))
    );

    // Output equals a only in the 2'b01 select case.
    check_a_only_in_01: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        (out_always == a) |=> ((sel_b2 == 1'b0) && (sel_b1 == 1'b1))
    );

    // If sel_b2 is 1, output must be b regardless of sel_b1.
    check_sel_b2_dominates_b: assert property (
        @(posedge a or negedge a or posedge b or negedge b or posedge sel_b1 or negedge sel_b1 or posedge sel_b2 or negedge sel_b2)
        (sel_b2 == 1'b1) |=> (out_always == b)
    );

endmodule