module RegisterAdd_4_sva (
    input logic       CLK,
    input logic       reset,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out
);

// Reset clears the register on the next sampled cycle.
    check_reset_clears_out: assert property (
        @(posedge CLK) reset |=> (out == 4'd0)
    );

// When not in reset, the next sampled output equals the previous cycle's inputs.
    check_addition_when_not_reset: assert property (
        @(posedge CLK) disable iff (reset) 1'b1 |=> (out == ($past(in1) + $past(in2)))
    );

// Zero on in1 passes in2 through on the next sampled cycle.
    check_zero_in1_passthrough: assert property (
        @(posedge CLK) disable iff (reset) (in1 == 4'd0) |=> (out == $past(in2))
    );

// Zero on in2 passes in1 through on the next sampled cycle.
    check_zero_in2_passthrough: assert property (
        @(posedge CLK) disable iff (reset) (in2 == 4'd0) |=> (out == $past(in1))
    );

// Maximum inputs wrap to zero on the next sampled cycle.
    check_max_inputs_wrap: assert property (
        @(posedge CLK) disable iff (reset) ((in1 == 4'hF) && (in2 == 4'hF)) |=> (out == 4'h0)
    );

endmodule
