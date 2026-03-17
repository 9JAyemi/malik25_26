module BusHold_assertions #(
    parameter n = 8
) (
    input logic [n-1:0] in,
    input logic         clk,
    input logic         rst,
    input logic [n-1:0] out
);

    // Out captures the previous input after an active cycle.
    check_capture_after_active_cycle: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst)) |-> (out == $past(in))
    );

    // Out is zero on the first non-reset cycle after reset.
    check_zero_after_reset_cycle: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && $past(rst)) |-> (out == '0)
    );

    // Stable inputs across active cycles keep the output stable one cycle later.
    check_stable_input_gives_stable_output: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst) && (in == $past(in))) |=> (out == $past(out))
    );

    // Changed inputs across active cycles change the output one cycle later.
    check_changed_input_changes_output: assert property (
        @(posedge clk) disable iff (rst)
        (!$initstate && !$past(rst) && (in != $past(in))) |=> (out != $past(out))
    );

endmodule