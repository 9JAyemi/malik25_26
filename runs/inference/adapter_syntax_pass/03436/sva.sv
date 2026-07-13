module oh_mux4_sva #(parameter DW = 1) (
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

    // out must match the RTL mux equation.
    check_mux_equation: assert property (
        @($global_clock)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3))
    );

    // When sel0 is high, out must equal in0.
    check_sel0_routes_in0: assert property (
        @($global_clock)
        sel0 |-> (out == in0)
    );

    // When sel1 is high, out must equal in1.
    check_sel1_routes_in1: assert property (
        @($global_clock)
        sel1 |-> (out == in1)
    );

    // When sel2 is high, out must equal in2.
    check_sel2_routes_in2: assert property (
        @($global_clock)
        sel2 |-> (out == in2)
    );

    // When sel3 is high, out must equal in3.
    check_sel3_routes_in3: assert property (
        @($global_clock)
        sel3 |-> (out == in3)
    );

    // When no select is high, out must be zero.
    check_no_selects_zero: assert property (
        @($global_clock)
        !(sel0 || sel1 || sel2 || sel3) |-> (out == {DW{1'b0}})
    );

    // When only sel0 and sel1 are high, out must equal in0.
    check_sel01_routes_in0: assert property (
        @($global_clock)
        (sel0 && sel1 && !sel2 && !sel3) |-> (out == in0)
    );

    // When only sel0 and sel2 are high, out must equal in0.
    check_sel02_routes_in0: assert property (
        @($global_clock)
        (sel0 && !sel1 && sel2 && !sel3) |-> (out == in0)
    );

    // When only sel0 and sel3 are high, out must equal in0.
    check_sel03_routes_in0: assert property (
        @($global_clock)
        (sel0 && !sel1 && !sel2 && sel3) |-> (out == in0)
    );

    // When only sel1 and sel2 are high, out must equal in1.
    check_sel12_routes_in1: assert property (
        @($global_clock)
        (!sel0 && sel1 && sel2 && !sel3) |-> (out == in1)
    );

    // When only sel1 and sel3 are high, out must equal in1.
    check_sel13_routes_in1: assert property (
        @($global_clock)
        (!sel0 && sel1 && !sel2 && sel3) |-> (out == in1)
    );

    // When only sel2 and sel3 are high, out must equal in2.
    check_sel23_routes_in2: assert property (
        @($global_clock)
        (!sel0 && !sel1 && sel2 && sel3) |-> (out == in2)
    );

endmodule