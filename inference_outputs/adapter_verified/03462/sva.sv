module oh_mux8_sva (
    input logic clk,
    input logic sel7,
    input logic sel6,
    input logic sel5,
    input logic sel4,
    input logic sel3,
    input logic sel2,
    input logic sel1,
    input logic sel0,
    input logic [DW-1:0] in7,
    input logic [DW-1:0] in6,
    input logic [DW-1:0] in5,
    input logic [DW-1:0] in4,
    input logic [DW-1:0] in3,
    input logic [DW-1:0] in2,
    input logic [DW-1:0] in1,
    input logic [DW-1:0] in0,
    input logic [DW-1:0] out
);

// No reset in RTL; assertions are sampled on clk.

    // out equals the RTL sum-of-products mux equation.
    check_full_mux_equation: assert property (
        @(posedge clk)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3) |
                ({DW{sel4}} & in4) |
                ({DW{sel5}} & in5) |
                ({DW{sel6}} & in6) |
                ({DW{sel7}} & in7))
    );

// When sel0 is high, out equals in0.
    check_sel0_routes_in0: assert property (
        @(posedge clk)
        sel0 |-> (out == in0)
    );

// When sel1 is high, out equals in1.
    check_sel1_routes_in1: assert property (
        @(posedge clk)
        sel1 |-> (out == in1)
    );

// When sel2 is high, out equals in2.
    check_sel2_routes_in2: assert property (
        @(posedge clk)
        sel2 |-> (out == in2)
    );

// When sel3 is high, out equals in3.
    check_sel3_routes_in3: assert property (
        @(posedge clk)
        sel3 |-> (out == in3)
    );

// When sel4 is high, out equals in4.
    check_sel4_routes_in4: assert property (
        @(posedge clk)
        sel4 |-> (out == in4)
    );

// When sel5 is high, out equals in5.
    check_sel5_routes_in5: assert property (
        @(posedge clk)
        sel5 |-> (out == in5)
    );

// When sel6 is high, out equals in6.
    check_sel6_routes_in6: assert property (
        @(posedge clk)
        sel6 |-> (out == in6)
    );

// When sel7 is high, out equals in7.
    check_sel7_routes_in7: assert property (
        @(posedge clk)
        sel7 |-> (out == in7)
    );

// When all selects are low, out is zero.
    check_no_selects_zero: assert property (
        @(posedge clk)
        !(sel0 || sel1 || sel2 || sel3 || sel4 || sel5 || sel6 || sel7) |-> (out == 0)
    );

// When exactly one select is high, out equals the selected input.
    check_single_select_routes_input: assert property (
        @(posedge clk)
        $onehot({sel7, sel6, sel5, sel4, sel3, sel2, sel1, sel0}) |-> (
            (sel0 ? (out == in0) : 1'b0) ||
            (sel1 ? (out == in1) : 1'b0) ||
            (sel2 ? (out == in2) : 1'b0) ||
            (sel3 ? (out == in3) : 1'b0) ||
            (sel4 ? (out == in4) : 1'b0) ||
            (sel5 ? (out == in5) : 1'b0) ||
            (sel6 ? (out == in6) : 1'b0) ||
            (sel7 ? (out == in7) : 1'b0)
        )
    );

endmodule
