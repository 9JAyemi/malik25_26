module RegisterAdd_4_sva (
    input logic CLK,
    input logic reset,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] out
);
    // Clock: CLK (posedge). Reset: reset (synchronous, active-high). Sequential register with 1-cycle add on non-reset.

    // On reset, out is cleared to 0 on the next cycle.
    reset_clears_out_next: assert property (
        @(posedge CLK) reset |=> (out == 4'd0)
    );

    // When not in reset, out equals the sum of in1 and in2 from the previous cycle.
    add_on_nonreset: assert property (
        @(posedge CLK) disable iff (reset) out == $past(in1 + in2)
    );

    // If previous cycle was not in reset and in1/in2 were stable, out remains stable.
    stable_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in1) == $past(in1,2)) && ($past(in2) == $past(in2,2)))
            |-> (out == $past(out))
    );

    // If previous cycle was not in reset and in1/in2 changed, out changes accordingly.
    change_when_inputs_change: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && (($past(in1) != $past(in1,2)) || ($past(in2) != $past(in2,2))))
            |-> (out != $past(out))
    );

    // If previous cycle was not in reset and in1/in2 were zero, out is zero.
    zero_when_inputs_zero: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in1) == 4'd0) && ($past(in2) == 4'd0))
            |-> (out == 4'd0)
    );

    // If previous cycle was not in reset and in1/in2 were 4'hF, out is 4'hE (mod 16).
    max_when_inputs_max: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in1) == 4'hF) && ($past(in2) == 4'hF))
            |-> (out == 4'hE)
    );

    // If previous cycle was not in reset and in1 was zero, out equals previous in2.
    pass_in2_when_in1_zero: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in1) == 4'd0))
            |-> (out == $past(in2))
    );

    // If previous cycle was not in reset and in2 was zero, out equals previous in1.
    pass_in1_when_in2_zero: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in2) == 4'd0))
            |-> (out == $past(in1))
    );

    // If previous cycle was not in reset and in1/in2 were equal, out equals in1<<1 (mod 16).
    double_when_inputs_equal: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in1) == $past(in2)))
            |-> (out == ($past(in1) << 1))
    );

    // If previous cycle was not in reset and in1 was 4'hF, out equals (in2-1) (mod 16).
    decrement_when_in1_max: assert property (
        @(posedge CLK) disable iff (reset)
            (!$past(reset) && ($past(in1) == 4'hF))
            |-> (out == ($past(in2) - 4'd1))
    );
endmodule