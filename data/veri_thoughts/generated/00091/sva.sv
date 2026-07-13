module mux4to1_sva (
    input logic [7:0] out,
    input logic [7:0] in0,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    input logic sel0,
    input logic sel1
);

    // Clockless combinational checks are sampled on the global formal clock.

    // When select is 00, the output must match in0.
    check_route_in0: assert property (
        @($global_clock) ({sel1, sel0} === 2'b00) |-> (out === in0)
    );

    // When select is 01, the output must match in1.
    check_route_in1: assert property (
        @($global_clock) ({sel1, sel0} === 2'b01) |-> (out === in1)
    );

    // When select is 10, the output must match in2.
    check_route_in2: assert property (
        @($global_clock) ({sel1, sel0} === 2'b10) |-> (out === in2)
    );

    // When select is 11, the output must match in3.
    check_route_in3: assert property (
        @($global_clock) ({sel1, sel0} === 2'b11) |-> (out === in3)
    );

    // With select held at 00 and in0 stable, other inputs must not affect out.
    check_stable_out_for_sel00: assert property (
        @($global_clock) (({sel1, sel0} === 2'b00) && $stable({sel1, sel0, in0})) |-> $stable(out)
    );

    // With select held at 01 and in1 stable, other inputs must not affect out.
    check_stable_out_for_sel01: assert property (
        @($global_clock) (({sel1, sel0} === 2'b01) && $stable({sel1, sel0, in1})) |-> $stable(out)
    );

    // With select held at 10 and in2 stable, other inputs must not affect out.
    check_stable_out_for_sel10: assert property (
        @($global_clock) (({sel1, sel0} === 2'b10) && $stable({sel1, sel0, in2})) |-> $stable(out)
    );

    // With select held at 11 and in3 stable, other inputs must not affect out.
    check_stable_out_for_sel11: assert property (
        @($global_clock) (({sel1, sel0} === 2'b11) && $stable({sel1, sel0, in3})) |-> $stable(out)
    );

endmodule