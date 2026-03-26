module mux_4to1_sva (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    input logic [7:0] in4,
    input logic       sel0,
    input logic       sel1,
    input logic [7:0] out
);

    // sel0=0 and sel1=0 route in1 to out.
    check_sel0_0_sel1_0_routes_in1: assert property (
        @($global_clock) ((sel0 === 1'b0) && (sel1 === 1'b0)) |-> (out === in1)
    );

    // sel0=1 and sel1=0 route in2 to out.
    check_sel0_1_sel1_0_routes_in2: assert property (
        @($global_clock) ((sel0 === 1'b1) && (sel1 === 1'b0)) |-> (out === in2)
    );

    // sel0=0 and sel1=1 route in3 to out.
    check_sel0_0_sel1_1_routes_in3: assert property (
        @($global_clock) ((sel0 === 1'b0) && (sel1 === 1'b1)) |-> (out === in3)
    );

    // sel0=1 and sel1=1 route in4 to out.
    check_sel0_1_sel1_1_routes_in4: assert property (
        @($global_clock) ((sel0 === 1'b1) && (sel1 === 1'b1)) |-> (out === in4)
    );

endmodule