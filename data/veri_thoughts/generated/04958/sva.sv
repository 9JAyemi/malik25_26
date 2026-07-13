module accumulator_sva #(parameter n = 8) (
    input logic clk,
    input logic rst,
    input logic [n-1:0] in,
    input logic [n-1:0] out
);

    // Output is zero whenever reset is asserted.
    check_out_zero_during_reset: assert property (
        @(posedge clk) rst |-> (out == '0)
    );

    // A reset cycle clears the stored value for the next cycle.
    check_reset_clears_output: assert property (
        @(posedge clk) rst |=> (out == '0)
    );

    // In normal operation, output adds the previous input each cycle.
    check_accumulate_when_running: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst)) |-> (out == ($past(out) + $past(in)))
    );

    // A zero input leaves the accumulated output unchanged.
    check_hold_on_zero_input: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst) && ($past(in) == '0)) |-> (out == $past(out))
    );

    // The first accumulation after reset starts from zero.
    check_first_add_after_reset: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(rst)) |=> (out == $past(in))
    );

endmodule