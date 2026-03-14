module mux_4to1_sva (
    input logic clk,
    input logic sel1,
    input logic sel2,
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic out
);

    ///// Functional mapping /////
    // When sel==00, out equals d0.
    check_map_sel00_to_d0: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b00) |-> (out == d0)
    );
    // When sel==01, out equals d1.
    check_map_sel01_to_d1: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b01) |-> (out == d1)
    );
    // When sel==10, out equals d2.
    check_map_sel10_to_d2: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b10) |-> (out == d2)
    );
    // When sel==11, out equals d3.
    check_map_sel11_to_d3: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b11) |-> (out == d3)
    );

    ///// Independence from unselected inputs /////
    // With sel==00 held constant and d0 stable, out is stable.
    check_stable_out_when_sel00_and_d0_stable: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b00 && $stable(sel1) && $stable(sel2) && $stable(d0)) |-> $stable(out)
    );
    // With sel==01 held constant and d1 stable, out is stable.
    check_stable_out_when_sel01_and_d1_stable: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b01 && $stable(sel1) && $stable(sel2) && $stable(d1)) |-> $stable(out)
    );
    // With sel==10 held constant and d2 stable, out is stable.
    check_stable_out_when_sel10_and_d2_stable: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b10 && $stable(sel1) && $stable(sel2) && $stable(d2)) |-> $stable(out)
    );
    // With sel==11 held constant and d3 stable, out is stable.
    check_stable_out_when_sel11_and_d3_stable: assert property (
        @(posedge clk) ({sel1, sel2} == 2'b11 && $stable(sel1) && $stable(sel2) && $stable(d3)) |-> $stable(out)
    );

endmodule