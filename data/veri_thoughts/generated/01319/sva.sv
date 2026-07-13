module adder_sva (
    input logic clk,
    input logic rst_n,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [8:0] out
);
    // When reset is asserted, out is driven to zero.
    reset_clears_out: assert property (
        @(posedge clk) !rst_n |-> (out == 9'd0)
    );

    // Out equals previous cycle's zero-extended sum when not in reset.
    out_matches_prev_sum: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) == 1'b1) |-> (out == $past({1'b0, in1} + {1'b0, in2}))
    );

    // Out is within the valid sum range [0..510] after an active cycle.
    out_within_range: assert property (
        @(posedge clk) disable iff (!rst_n) ($past(rst_n) == 1'b1) |-> (out <= 9'd510)
    );

    // If inputs are unchanged over two cycles, out remains unchanged.
    out_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (!rst_n)
            (($past(rst_n) == 1'b1) && ($past(rst_n,2) == 1'b1) &&
             ($past(in1) == $past(in1,2)) && ($past(in2) == $past(in2,2)))
            |-> (out == $past(out))
    );

    // If previous inputs were both zero, next out is zero.
    zero_inputs_zero_output: assert property (
        @(posedge clk) disable iff (!rst_n)
            (($past(rst_n) == 1'b1) && ($past(in1) == 8'd0) && ($past(in2) == 8'd0))
            |-> (out == 9'd0)
    );

    // If previous inputs were both 0xFF, next out is 510.
    max_inputs_max_output: assert property (
        @(posedge clk) disable iff (!rst_n)
            (($past(rst_n) == 1'b1) && ($past(in1) == 8'hFF) && ($past(in2) == 8'hFF))
            |-> (out == 9'd510)
    );

    // With no carry from previous inputs, MSB is 0 and low byte is 8-bit sum.
    no_carry_decomposition: assert property (
        @(posedge clk) disable iff (!rst_n)
            (($past(rst_n) == 1'b1) &&
             ((({1'b0, $past(in1)} + {1'b0, $past(in2)})[8]) == 1'b0))
            |-> ((out[8] == 1'b0) && (out[7:0] == ($past(in1) + $past(in2))))
    );

    // With carry from previous inputs, MSB is 1 and low byte is 8-bit sum.
    carry_decomposition: assert property (
        @(posedge clk) disable iff (!rst_n)
            (($past(rst_n) == 1'b1) &&
             ((({1'b0, $past(in1)} + {1'b0, $past(in2)})[8]) == 1'b1))
            |-> ((out[8] == 1'b1) && (out[7:0] == ($past(in1) + $past(in2))))
    );
endmodule