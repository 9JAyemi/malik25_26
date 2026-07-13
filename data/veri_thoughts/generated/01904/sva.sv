module Mealy_sva #(
    parameter int n = 4,
    parameter int m = 2,
    parameter int s = 3
) (
    input logic clk,
    input logic [n-1:0] in,
    input logic [m-1:0] out,
    input logic [s-1:0] state,
    input logic [s-1:0] next_state,
    input logic [m-1:0] output_next
);

    ///// Combinational next_state/output_next mapping /////
    // In state 0 with in[0]&in[1], next_state=1 and output_next=2'b10.
    comb_map_s0_t: assert property (
        @(posedge clk) (state == '0) && (in[0] && in[1]) |-> (next_state == '1) && (output_next == 2'b10)
    );
    // In state 0 with !(in[0]&in[1]), next_state=2 and output_next=2'b01.
    comb_map_s0_f: assert property (
        @(posedge clk) (state == '0) && !(in[0] && in[1]) |-> (next_state == '2) && (output_next == 2'b01)
    );
    // In state 1 with in[2], next_state=0 and output_next=2'b01.
    comb_map_s1_t: assert property (
        @(posedge clk) (state == '1) && in[2] |-> (next_state == '0) && (output_next == 2'b01)
    );
    // In state 1 with !in[2], next_state=2 and output_next=2'b00.
    comb_map_s1_f: assert property (
        @(posedge clk) (state == '1) && !in[2] |-> (next_state == '2) && (output_next == 2'b00)
    );
    // In state 2 with in[3], next_state=0 and output_next=2'b11.
    comb_map_s2_t: assert property (
        @(posedge clk) (state == '2) && in[3] |-> (next_state == '0) && (output_next == 2'b11)
    );
    // In state 2 with !in[3], next_state=1 and output_next=2'b00.
    comb_map_s2_f: assert property (
        @(posedge clk) (state == '2) && !in[3] |-> (next_state == '1) && (output_next == 2'b00)
    );
    // In any other state, next_state=0 and output_next=2'b00.
    comb_map_default: assert property (
        @(posedge clk) (state != '0) && (state != '1) && (state != '2) |-> (next_state == '0) && (output_next == 2'b00)
    );

    ///// Sequential register updates derived from previous state/input /////
    // From prev state 0 with in[0]&in[1], state->1 and out->2'b10.
    seq_s0_t: assert property (
        @(posedge clk) $past((state == '0) && (in[0] && in[1]), 1, 1'b0) |-> (state == '1) && (out == 2'b10)
    );
    // From prev state 0 with !(in[0]&in[1]), state->2 and out->2'b01.
    seq_s0_f: assert property (
        @(posedge clk) $past((state == '0) && !(in[0] && in[1]), 1, 1'b0) |-> (state == '2) && (out == 2'b01)
    );
    // From prev state 1 with in[2], state->0 and out->2'b01.
    seq_s1_t: assert property (
        @(posedge clk) $past((state == '1) && in[2], 1, 1'b0) |-> (state == '0) && (out == 2'b01)
    );
    // From prev state 1 with !in[2], state->2 and out->2'b00.
    seq_s1_f: assert property (
        @(posedge clk) $past((state == '1) && !in[2], 1, 1'b0) |-> (state == '2) && (out == 2'b00)
    );
    // From prev state 2 with in[3], state->0 and out->2'b11.
    seq_s2_t: assert property (
        @(posedge clk) $past((state == '2) && in[3], 1, 1'b0) |-> (state == '0) && (out == 2'b11)
    );
    // From prev state 2 with !in[3], state->1 and out->2'b00.
    seq_s2_f: assert property (
        @(posedge clk) $past((state == '2) && !in[3], 1, 1'b0) |-> (state == '1) && (out == 2'b00)
    );
    // From any other prev state, state->0 and out->2'b00.
    seq_default: assert property (
        @(posedge clk) $past(((state != '0) && (state != '1) && (state != '2)), 1, 1'b0) |-> (state == '0) && (out == 2'b00)
    );

endmodule