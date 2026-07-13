module oh_mux8_sva #(parameter DW = 1) (
    input logic          sel7,
    input logic          sel6,
    input logic          sel5,
    input logic          sel4,
    input logic          sel3,
    input logic          sel2,
    input logic          sel1,
    input logic          sel0,
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

    // Output must match the masked-OR of all selected inputs.
    check_output_masked_or: assert property (
        @($global_clock)
        out == (({DW{sel0}} & in0) |
                ({DW{sel1}} & in1) |
                ({DW{sel2}} & in2) |
                ({DW{sel3}} & in3) |
                ({DW{sel4}} & in4) |
                ({DW{sel5}} & in5) |
                ({DW{sel6}} & in6) |
                ({DW{sel7}} & in7))
    );

    // With no selects asserted, the output must be zero.
    check_no_select_zero: assert property (
        @($global_clock)
        (!sel7 && !sel6 && !sel5 && !sel4 && !sel3 && !sel2 && !sel1 && !sel0) |-> (out == {DW{1'b0}})
    );

    // With only sel0 asserted, the output must equal in0.
    check_only_sel0_routes_in0: assert property (
        @($global_clock)
        (!sel7 && !sel6 && !sel5 && !sel4 && !sel3 && !sel2 && !sel1 && sel0) |-> (out == in0)
    );

    // With only sel1 asserted, the output must equal in1.
    check_only_sel1_routes_in1: assert property (
        @($global_clock)
        (!sel7 && !sel6 && !sel5 && !sel4 && !sel3 && !sel2 && sel1 && !sel0) |-> (out == in1)
    );

    // With only sel2 asserted, the output must equal in2.
    check_only_sel2_routes_in2: assert property (
        @($global_clock)
        (!sel7 && !sel6 && !sel5 && !sel4 && !sel3 && sel2 && !sel1 && !sel0) |-> (out == in2)
    );

    // With only sel3 asserted, the output must equal in3.
    check_only_sel3_routes_in3: assert property (
        @($global_clock)
        (!sel7 && !sel6 && !sel5 && !sel4 && sel3 && !sel2 && !sel1 && !sel0) |-> (out == in3)
    );

    // With only sel4 asserted, the output must equal in4.
    check_only_sel4_routes_in4: assert property (
        @($global_clock)
        (!sel7 && !sel6 && !sel5 && sel4 && !sel3 && !sel2 && !sel1 && !sel0) |-> (out == in4)
    );

    // With only sel5 asserted, the output must equal in5.
    check_only_sel5_routes_in5: assert property (
        @($global_clock)
        (!sel7 && !sel6 && sel5 && !sel4 && !sel3 && !sel2 && !sel1 && !sel0) |-> (out == in5)
    );

    // With only sel6 asserted, the output must equal in6.
    check_only_sel6_routes_in6: assert property (
        @($global_clock)
        (!sel7 && sel6 && !sel5 && !sel4 && !sel3 && !sel2 && !sel1 && !sel0) |-> (out == in6)
    );

    // With only sel7 asserted, the output must equal in7.
    check_only_sel7_routes_in7: assert property (
        @($global_clock)
        (sel7 && !sel6 && !sel5 && !sel4 && !sel3 && !sel2 && !sel1 && !sel0) |-> (out == in7)
    );

endmodule