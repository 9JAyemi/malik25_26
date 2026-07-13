module edge_detector_sva (
    input logic clk,
    input logic [15:0] in,
    input logic [15:0] anyedge
);
    // On LSB falling edge, capture the entire input vector on the next cycle.
    capture_on_lsb_fall_copies_in: assert property (
        @(posedge clk) $fell(in[0]) |=> (anyedge == $past(in))
    );

    // On LSB falling edge, captured LSB is 0 on the next cycle.
    capture_on_lsb_fall_lsb_zero: assert property (
        @(posedge clk) $fell(in[0]) |=> (anyedge[0] == 1'b0)
    );

    // Without an LSB falling edge, anyedge holds its previous value.
    no_update_without_lsb_fall: assert property (
        @(posedge clk) !$fell(in[0]) |=> (anyedge == $past(anyedge))
    );

    // anyedge can change only if the previous cycle had an LSB falling edge.
    update_only_after_previous_lsb_fall: assert property (
        @(posedge clk) $changed(anyedge) |-> $past($fell(in[0]))
    );

    // If anyedge changes, its new value equals the previous cycle's input.
    update_value_matches_prev_in: assert property (
        @(posedge clk) $changed(anyedge) |-> (anyedge == $past(in))
    );

    // An LSB rising edge does not update anyedge on the next cycle.
    rise_no_capture: assert property (
        @(posedge clk) $rose(in[0]) |=> (anyedge == $past(anyedge))
    );
endmodule