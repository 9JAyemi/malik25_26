module oh_mux4_sva (
    input logic clk,
    input logic sel3,
    input logic sel2,
    input logic sel1,
    input logic sel0,
    input logic [DW-1:0] in3,
    input logic [DW-1:0] in2,
    input logic [DW-1:0] in1,
    input logic [DW-1:0] in0,
    input logic [DW-1:0] out
);

// No RTL clock or reset; sample this combinational logic on clk.

    // out must match the RTL's full combinational equation.
    check_full_mux_equation: assert property (
        @(posedge clk)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3))
    );

// When sel0 is high, out must equal in0.
    check_sel0_routes_in0: assert property (
        @(posedge clk)
        sel0 |-> (out == in0)
    );

// When sel1 is high, out must equal in1.
    check_sel1_routes_in1: assert property (
        @(posedge clk)
        sel1 |-> (out == in1)
    );

// When sel2 is high, out must equal in2.
    check_sel2_routes_in2: assert property (
        @(posedge clk)
        sel2 |-> (out == in2)
    );

// When sel3 is high, out must equal in3.
    check_sel3_routes_in3: assert property (
        @(posedge clk)
        sel3 |-> (out == in3)
    );

// When all selects are low, out must be zero.
    check_all_zero_when_no_selects: assert property (
        @(posedge clk)
        !(sel0 | sel1 | sel2 | sel3) |-> (out == 0)
    );

// When exactly one select is high, out must equal the selected input.
    check_onehot_select_routes_input: assert property (
        @(posedge clk)
        $onehot({sel3, sel2, sel1, sel0}) |-> (out == (sel0 ? in0 : (sel1 ? in1 : (sel2 ? in2 : in3))))
    );

// When more than one select is high, out must be zero.
    check_zero_when_multiple_selects: assert property (
        @(posedge clk)
        (sel0 & sel1) || (sel0 & sel2) || (sel0 & sel3) || (sel1 & sel2) || (sel1 & sel3) || (sel2 & sel3) |-> (out == 0)
    );

endmodule
