module DEMUX_sva #(parameter int m = 3) (
    input logic in,
    input logic [m-1:0] sel,
    input logic [(2**m)-1:0] out
);

    localparam int OUT_W = 2**m;
    genvar i;

    // No clock exists in the RTL; sample on the formal global clock.
    // No reset exists in the RTL.
    // The DUT is purely combinational.

    generate
        for (i = 0; i < OUT_W; i = i + 1) begin : gen_route_checks
            // The selected output bit mirrors the input.
            check_selected_route: assert property (
                @($global_clock) (sel == i) |-> (out[i] == in)
            );

            // Any unselected output bit remains low.
            check_unselected_low: assert property (
                @($global_clock) (sel != i) |-> (out[i] == 1'b0)
            );
        end
    endgenerate

    // A low input forces all outputs low.
    check_zero_input_clears_outputs: assert property (
        @($global_clock) (in == 1'b0) |-> (out == '0)
    );

    // A high input produces exactly one asserted output bit.
    check_high_input_onehot: assert property (
        @($global_clock) (in == 1'b1) |-> $onehot(out)
    );

    // The output bus is never multi-hot.
    check_output_onehot0: assert property (
        @($global_clock) $onehot0(out)
    );

    // Any asserted output requires the input to be high.
    check_nonzero_output_requires_high_input: assert property (
        @($global_clock) (out != '0) |-> (in == 1'b1)
    );

endmodule