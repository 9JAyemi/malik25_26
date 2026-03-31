module mux_4_to_1_sva (
    input logic clk,
    input logic sel1,
    input logic sel2,
    input logic [3:0] d0,
    input logic [3:0] d1,
    input logic [3:0] d2,
    input logic [3:0] d3,
    input logic [3:0] out
);

    // out must match the RTL mux equation.
    check_mux_equation: assert property (
        @(posedge clk)
        out == ((sel1 & sel2) ? d3 :
                ((sel1 & ~sel2) ? d2 :
                 ((~sel1 & sel2) ? d1 : d0)))
    );

    // When sel1 and sel2 are both high, out must select d3.
    check_select_d3: assert property (
        @(posedge clk)
        (sel1 && sel2) |-> (out == d3)
    );

    // When sel1 is high and sel2 is low, out must select d2.
    check_select_d2: assert property (
        @(posedge clk)
        (sel1 && !sel2) |-> (out == d2)
    );

    // When sel1 is low and sel2 is high, out must select d1.
    check_select_d1: assert property (
        @(posedge clk)
        (!sel1 && sel2) |-> (out == d1)
    );

    // When both select bits are low, out must select d0.
    check_select_d0: assert property (
        @(posedge clk)
        (!sel1 && !sel2) |-> (out == d0)
    );

endmodule