module comb_circuit_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [2:0] out
);
    // Analysis: No reset; combinational logic only; sample assertions on an external clock.
    // Behavior: out = (in < 4) ? (in + 1)[2:0] : (in - 1)[2:0].

    // For in < 4, out equals in + 1 (3-bit result).
    check_low_range_function: assert property (
        @(posedge clk) (in < 4'd4) |-> (out == (in[2:0] + 3'd1))
    );

    // For in >= 4, out equals in - 1 (3-bit result).
    check_high_range_function: assert property (
        @(posedge clk) (in >= 4'd4) |-> (out == (in[2:0] - 3'd1))
    );

    // Boundary: in == 3 maps to out == 4.
    check_boundary_in3_out4: assert property (
        @(posedge clk) (in == 4'd3) |-> (out == 3'd4)
    );

    // Boundary: in == 4 maps to out == 3.
    check_boundary_in4_out3: assert property (
        @(posedge clk) (in == 4'd4) |-> (out == 3'd3)
    );

    // Corner: in == 0 maps to out == 1.
    check_in0_out1: assert property (
        @(posedge clk) (in == 4'd0) |-> (out == 3'd1)
    );

    // If input is stable across a cycle, output must be stable.
    check_out_stable_if_in_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(out)
    );

    // In low range, if input increments by 1 and stays <4, output increments by 1.
    check_inc_in_low_range_updates_out: assert property (
        @(posedge clk) (($past(in) < 4'd4) && (in < 4'd4) && (in == $past(in) + 4'd1)) |-> (out == $past(out) + 3'd1)
    );

    // In low range, if input decrements by 1 and stays <4, output decrements by 1.
    check_dec_in_low_range_updates_out: assert property (
        @(posedge clk) (($past(in) < 4'd4) && (in < 4'd4) && ($past(in) == in + 4'd1)) |-> (out == $past(out) - 3'd1)
    );

    // In high range, if input increments by 1 and stays >=4, output increments by 1.
    check_inc_in_high_range_updates_out: assert property (
        @(posedge clk) (($past(in) >= 4'd4) && (in >= 4'd4) && (in == $past(in) + 4'd1)) |-> (out == $past(out) + 3'd1)
    );

    // In high range, if input decrements by 1 and stays >=4, output decrements by 1.
    check_dec_in_high_range_updates_out: assert property (
        @(posedge clk) (($past(in) >= 4'd4) && (in >= 4'd4) && ($past(in) == in + 4'd1)) |-> (out == $past(out) - 3'd1)
    );
endmodule