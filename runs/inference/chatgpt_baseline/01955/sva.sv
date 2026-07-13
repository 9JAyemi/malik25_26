module mux4to1_32_sva (
    input logic clk,                 // external clock for SVA sampling
    input logic [1:0] sel,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [31:0] c,
    input logic [31:0] d,
    input logic [31:0] o
);
    // sel==00 routes a to o.
    check_sel00_routes_a: assert property (
        @(posedge clk) (sel == 2'b00) |-> (o === a)
    );

    // sel==01 routes b to o.
    check_sel01_routes_b: assert property (
        @(posedge clk) (sel == 2'b01) |-> (o === b)
    );

    // sel==10 routes c to o.
    check_sel10_routes_c: assert property (
        @(posedge clk) (sel == 2'b10) |-> (o === c)
    );

    // sel==11 routes d to o.
    check_sel11_routes_d: assert property (
        @(posedge clk) (sel == 2'b11) |-> (o === d)
    );

    // For known sel, o equals the selected input (single-expression form).
    check_function_when_sel_known: assert property (
        @(posedge clk) (!$isunknown(sel)) |-> (o === ((sel==2'b00) ? a :
                                                     (sel==2'b01) ? b :
                                                     (sel==2'b10) ? c : d))
    );

    // If sel==00 and both sel and a are stable, o is stable.
    check_stable_o_when_sel00_a_stable: assert property (
        @(posedge clk) (sel == 2'b00 && $stable(sel) && $stable(a)) |-> $stable(o)
    );

    // If sel==01 and both sel and b are stable, o is stable.
    check_stable_o_when_sel01_b_stable: assert property (
        @(posedge clk) (sel == 2'b01 && $stable(sel) && $stable(b)) |-> $stable(o)
    );

    // If sel==10 and both sel and c are stable, o is stable.
    check_stable_o_when_sel10_c_stable: assert property (
        @(posedge clk) (sel == 2'b10 && $stable(sel) && $stable(c)) |-> $stable(o)
    );

    // If sel==11 and both sel and d are stable, o is stable.
    check_stable_o_when_sel11_d_stable: assert property (
        @(posedge clk) (sel == 2'b11 && $stable(sel) && $stable(d)) |-> $stable(o)
    );

    // If all known and o changes, either sel changed or the selected input changed.
    check_o_change_has_cause: assert property (
        @(posedge clk)
            (!$isunknown({sel,a,b,c,d,o}) && $changed(o)) |-> 
            ( !$stable(sel)
              || ((sel==2'b00) && !$stable(a))
              || ((sel==2'b01) && !$stable(b))
              || ((sel==2'b10) && !$stable(c))
              || ((sel==2'b11) && !$stable(d)) )
    );
endmodule