module rising_edge_detector_sva (
    input logic clk,
    input logic [31:0] in,
    input logic [31:0] out,
    input logic [31:0] prev_in
);
    // Clock: clk; No reset. Sequential edge detector: out pulses on 0->1 of in; prev_in stores prior in.

    // prev_in must equal the previous-cycle value of in.
    check_prev_in_tracks_in: assert property (
        @(posedge clk) disable iff ($initstate) prev_in == $past(in)
    );

    // out must equal the registered (in & ~prev_in) from the previous cycle.
    check_out_eq_registered_expr: assert property (
        @(posedge clk) disable iff ($initstate) out == $past(in & ~prev_in)
    );

    genvar i;
    for (i = 0; i < 32; i++) begin : gen_bit_sva
        // A rising edge on in[i] produces a pulse on out[i] in the next cycle.
        check_rise_produces_pulse: assert property (
            @(posedge clk) disable iff ($initstate) $rose(in[i]) |-> ##1 (out[i] == 1'b1)
        );

        // If no rising edge on in[i], out[i] is 0 in the next cycle.
        check_no_rise_no_pulse: assert property (
            @(posedge clk) disable iff ($initstate) !$rose(in[i]) |-> ##1 (out[i] == 1'b0)
        );

        // A pulse on out[i] is never back-to-back (single-cycle pulse).
        check_no_back_to_back_pulses: assert property (
            @(posedge clk) disable iff ($initstate) out[i] |-> ##1 !out[i]
        );

        // A pulse on out[i] implies in[i] was HIGH in the previous cycle.
        check_out_implies_prev_in_high: assert property (
            @(posedge clk) disable iff ($initstate) out[i] |-> $past(in[i])
        );
    end

endmodule