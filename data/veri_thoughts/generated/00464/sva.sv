module mux_4to1_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic sel0,
    input logic sel1,
    input logic out
);

    // When {sel1, sel0} is 2'b00, out follows in0.
    check_sel_00_routes_in0: assert property (
        @($global_clock) ((sel1 === 1'b0) && (sel0 === 1'b0)) |-> (out === in0)
    );

    // When {sel1, sel0} is 2'b01, out follows in1.
    check_sel_01_routes_in1: assert property (
        @($global_clock) ((sel1 === 1'b0) && (sel0 === 1'b1)) |-> (out === in1)
    );

    // When {sel1, sel0} is 2'b10, out follows in2.
    check_sel_10_routes_in2: assert property (
        @($global_clock) ((sel1 === 1'b1) && (sel0 === 1'b0)) |-> (out === in2)
    );

    // When {sel1, sel0} is 2'b11, out follows in3.
    check_sel_11_routes_in3: assert property (
        @($global_clock) ((sel1 === 1'b1) && (sel0 === 1'b1)) |-> (out === in3)
    );

endmodule