module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  in_edge,
    input logic        anyedge,
    input logic [7:0]  upper_byte,
    input logic [7:0]  lower_byte,
    input logic        upper_edge,
    input logic        lower_edge,
    input logic [7:0]  upper_prev_in,
    input logic [7:0]  lower_prev_in
);

    // Upper byte matches the high half of the input bus.
    check_upper_byte_split: assert property (
        @(posedge clk) disable iff ($initstate) upper_byte === in[15:8]
    );

    // Lower byte matches the low half of the input bus.
    check_lower_byte_split: assert property (
        @(posedge clk) disable iff ($initstate) lower_byte === in[7:0]
    );

    // The split bytes reconstruct the original input bus.
    check_input_reconstruction: assert property (
        @(posedge clk) disable iff ($initstate) {upper_byte, lower_byte} === in
    );

    // Upper edge detector state stores the previous upper byte.
    check_upper_prev_tracks_upper_byte: assert property (
        @(posedge clk) disable iff ($initstate) upper_prev_in === $past(upper_byte)
    );

    // Lower edge detector state stores the previous lower byte.
    check_lower_prev_tracks_lower_byte: assert property (
        @(posedge clk) disable iff ($initstate) lower_prev_in === $past(lower_byte)
    );

    // An upper-byte change raises upper_edge on the next cycle.
    check_upper_change_sets_upper_edge: assert property (
        @(posedge clk) disable iff ($initstate) (upper_byte != $past(upper_byte)) |=> upper_edge
    );

    // A stable upper byte clears upper_edge on the next cycle.
    check_upper_stable_clears_upper_edge: assert property (
        @(posedge clk) disable iff ($initstate) (upper_byte == $past(upper_byte)) |=> !upper_edge
    );

    // A lower-byte change raises lower_edge on the next cycle.
    check_lower_change_sets_lower_edge: assert property (
        @(posedge clk) disable iff ($initstate) (lower_byte != $past(lower_byte)) |=> lower_edge
    );

    // A stable lower byte clears lower_edge on the next cycle.
    check_lower_stable_clears_lower_edge: assert property (
        @(posedge clk) disable iff ($initstate) (lower_byte == $past(lower_byte)) |=> !lower_edge
    );

    // Any input-bus change raises at least one detector output on the next cycle.
    check_input_change_sets_some_edge: assert property (
        @(posedge clk) disable iff ($initstate) (in != $past(in)) |=> (upper_edge | lower_edge)
    );

    // A stable input bus clears both detector outputs on the next cycle.
    check_input_stable_clears_all_edges: assert property (
        @(posedge clk) disable iff ($initstate) (in == $past(in)) |=> !(upper_edge | lower_edge)
    );

    // When known, the top output matches the OR of the detector outputs.
    check_anyedge_matches_detector_or_when_known: assert property (
        @(posedge clk) disable iff ($initstate) !$isunknown(anyedge) |-> (anyedge == (upper_edge | lower_edge))
    );

endmodule