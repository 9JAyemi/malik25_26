module TwosComplement_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);
    // Out equals two's complement of previous input (one-cycle latency).
    check_out_twos_complement_prev_in: assert property (
        @(posedge clk) out == ((~$past(in)) + 4'd1)
    );

    // LSB of out matches previous LSB of in.
    check_lsb_matches_prev_in: assert property (
        @(posedge clk) out[0] == $past(in[0])
    );

    // Previous input 0 maps to output 0.
    check_prev_zero_maps_zero: assert property (
        @(posedge clk) ($past(in) == 4'h0) |-> (out == 4'h0)
    );

    // Previous input 8 maps to output 8.
    check_prev_eight_maps_eight: assert property (
        @(posedge clk) ($past(in) == 4'h8) |-> (out == 4'h8)
    );

    // Previous input 1 maps to output 15.
    check_prev_one_maps_fifteen: assert property (
        @(posedge clk) ($past(in) == 4'h1) |-> (out == 4'hF)
    );

    // Previous input 15 maps to output 1.
    check_prev_fifteen_maps_one: assert property (
        @(posedge clk) ($past(in) == 4'hF) |-> (out == 4'h1)
    );

    // Output equals previous input only for 0 or 8.
    check_prev_nonfixed_implies_notequal: assert property (
        @(posedge clk) (($past(in) != 4'h0) && ($past(in) != 4'h8)) |-> (out != $past(in))
    );

    // If input was stable last cycle, output remains stable this cycle.
    check_stable_in_prev_implies_stable_out: assert property (
        @(posedge clk) ($past(in) == $past(in,2)) |-> (out == $past(out))
    );

    // If input incremented by 1 (prev-to-prev), output decrements by 1 (prev-to-now).
    check_incr_by1_decr_out_by1: assert property (
        @(posedge clk) ($past(in) == ($past(in,2) + 4'd1)) |-> (out == ($past(out) - 4'd1))
    );

    // If input decremented by 1 (prev-to-prev), output increments by 1 (prev-to-now).
    check_decr_by1_incr_out_by1: assert property (
        @(posedge clk) ($past(in) == ($past(in,2) - 4'd1)) |-> (out == ($past(out) + 4'd1))
    );
endmodule