module four_bit_register_sva (
    input logic clk,
    input logic [3:0] din,
    input logic [3:0] dout
);
    // dout equals din from previous clock (1-cycle latency).
    check_dout_one_cycle_latency: assert property (
        @(posedge clk) !$isunknown($past(din)) |-> (dout == $past(din))
    );

    // A change on din causes a change on dout one cycle later.
    check_change_propagation: assert property (
        @(posedge clk) (!$isunknown($past(din)) && (din != $past(din))) |=> (dout != $past(dout))
    );

    // If din is stable between clocks, dout is stable on the next cycle.
    check_stability_propagation: assert property (
        @(posedge clk) (!$isunknown($past(din)) && (din == $past(din))) |=> (dout == $past(dout))
    );

    // Per-bit 1-cycle latency from din[i] to dout[i].
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_bit_latency
            // dout[i] equals din[i] from previous clock.
            check_bit_latency: assert property (
                @(posedge clk) !$isunknown($past(din[i])) |-> (dout[i] == $past(din[i]))
            );
        end
    endgenerate
endmodule