module binary_counter_sva (
    input logic clk,
    input logic rst,
    input logic [1:0] count,
    input logic overflow
);
    ///// Reset behavior /////
    // While reset is asserted low, count and overflow are held at 0.
    reset_outputs_zero: assert property (
        @(posedge clk) (rst == 1'b0) |-> (count == 2'b00) && (overflow == 1'b0)
    );

    ///// State transitions /////
    // From 00, next is 01 with no overflow.
    trans_00_to_01: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b00) |=> ((count == 2'b01) && (overflow == 1'b0))
    );
    // From 01, next is 10 with no overflow.
    trans_01_to_10: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b01) |=> ((count == 2'b10) && (overflow == 1'b0))
    );
    // From 10, next is 11 with no overflow.
    trans_10_to_11: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b10) |=> ((count == 2'b11) && (overflow == 1'b0))
    );
    // From 11, next is 00 and overflow asserted.
    trans_11_to_00_overflow: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b11) |=> ((count == 2'b00) && (overflow == 1'b1))
    );

    ///// Overflow semantics /////
    // Overflow high implies current count is 00.
    overflow_implies_zero: assert property (
        @(posedge clk) disable iff (!rst) overflow |-> (count == 2'b00)
    );
    // When count is nonzero, overflow must be 0.
    no_overflow_when_count_nonzero: assert property (
        @(posedge clk) disable iff (!rst) (count != 2'b00) |-> (overflow == 1'b0)
    );
    // Overflow is a single-cycle pulse.
    overflow_single_cycle: assert property (
        @(posedge clk) disable iff (!rst) overflow |=> !overflow
    );

    ///// Reset release /////
    // On reset deassertion, hold 00/0 then increment to 01/0.
    post_reset_first_step: assert property (
        @(posedge clk) $rose(rst) |-> ((count == 2'b00) && (overflow == 1'b0)) ##1 ((count == 2'b01) && (overflow == 1'b0))
    );

    ///// Multi-step progression /////
    // After wrap (11->00/overflow), next step is 01 with overflow low.
    wrap_two_step_progress: assert property (
        @(posedge clk) disable iff (!rst) (count == 2'b11) |=> ((count == 2'b00) && (overflow == 1'b1)) ##1 ((count == 2'b01) && (overflow == 1'b0))
    );
endmodule