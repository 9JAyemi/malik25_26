module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] OUT,
    input logic [3:0] counter_out
);

    // A reset cycle clears the registered adder output by the next clock.
    check_out_clears_after_reset: assert property (
        @(posedge clk) reset |=> (OUT == 4'b0000)
    );

    // The first add after reset release uses a cleared carry-in.
    check_first_add_after_reset_uses_zero_carry: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |=> ({1'b0, OUT} == (({1'b0, $past(A)} + {1'b0, $past(B)}) & 5'h0F))
    );

    // A zero adder output clears the counter on the next clock.
    check_counter_clears_on_zero_input: assert property (
        @(posedge clk) disable iff (reset)
        (OUT == 4'b0000) |=> (counter_out == 4'b0000)
    );

    // An all-ones adder output forces the counter to all ones on the next clock.
    check_counter_sets_on_all_ones_input: assert property (
        @(posedge clk) disable iff (reset)
        (OUT == 4'b1111) |=> (counter_out == 4'b1111)
    );

    // Other adder outputs shift the prior counter and append OUT[3].
    check_counter_shifts_on_intermediate_input: assert property (
        @(posedge clk) disable iff (reset)
        (OUT != 4'b0000 && OUT != 4'b1111) |=> (counter_out == {$past(counter_out[2:0]), $past(OUT[3])})
    );

    // Releasing reset leads to a zero counter one clock later because OUT is zero then.
    check_counter_clears_after_reset_release: assert property (
        @(posedge clk) disable iff (reset)
        $fell(reset) |=> (counter_out == 4'b0000)
    );

endmodule