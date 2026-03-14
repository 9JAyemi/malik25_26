module mux3ds_sva #(
    parameter SIZE = 1
) (
    // External sampling clock for assertions (DUT has no clock/reset).
    input  logic               CLK,

    // DUT ports
    input  logic [SIZE-1:0]    dout,
    input  logic [SIZE-1:0]    in0,
    input  logic [SIZE-1:0]    in1,
    input  logic [SIZE-1:0]    in2,
    input  logic               sel0,
    input  logic               sel1,
    input  logic               sel2
);
    // Combinational 3:1 mux: when exactly one sel is HIGH, dout equals that input.

    // When sel0=1 and sel1=sel2=0, dout equals in0.
    select0_maps_to_in0: assert property (
        @(posedge CLK) (sel0 && !sel1 && !sel2) |-> (dout == in0)
    );

    // When sel1=1 and sel0=sel2=0, dout equals in1.
    select1_maps_to_in1: assert property (
        @(posedge CLK) (sel1 && !sel0 && !sel2) |-> (dout == in1)
    );

    // When sel2=1 and sel0=sel1=0, dout equals in2.
    select2_maps_to_in2: assert property (
        @(posedge CLK) (sel2 && !sel0 && !sel1) |-> (dout == in2)
    );

    // If sel0 is the sole active select in two consecutive cycles and in0 is stable, dout is stable.
    select0_stability_when_in0_stable: assert property (
        @(posedge CLK) $past(sel0 && !sel1 && !sel2) && (sel0 && !sel1 && !sel2) && $stable(in0) |-> $stable(dout)
    );

    // If sel1 is the sole active select in two consecutive cycles and in1 is stable, dout is stable.
    select1_stability_when_in1_stable: assert property (
        @(posedge CLK) $past(sel1 && !sel0 && !sel2) && (sel1 && !sel0 && !sel2) && $stable(in1) |-> $stable(dout)
    );

    // If sel2 is the sole active select in two consecutive cycles and in2 is stable, dout is stable.
    select2_stability_when_in2_stable: assert property (
        @(posedge CLK) $past(sel2 && !sel0 && !sel1) && (sel2 && !sel0 && !sel1) && $stable(in2) |-> $stable(dout)
    );

endmodule