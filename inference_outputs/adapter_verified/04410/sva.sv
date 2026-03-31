module fifo_buffer_sva (
    input logic clk,
    input logic aclr,
    input logic [7:0] din,
    input logic [7:0] dout
);

// On reset assertion, all memory cells and dout are cleared.
    reset_clears_memory_and_dout: assert property (
        @(posedge clk) aclr |-> (dout == 8'h00)
    );

// On reset assertion, dout is driven to zero in the same cycle.
    reset_sets_dout_zero_now: assert property (
        @(posedge clk) aclr |-> (dout == 8'h00)
    );

// On reset assertion, the first memory cell captures din.
    reset_captures_din_to_mem0: assert property (
        @(posedge clk) aclr |-> (mem[0] == $past(din))
    );

// On reset assertion, the second memory cell remains zero.
    reset_keeps_mem1_zero: assert property (
        @(posedge clk) aclr |-> (mem[1] == 8'h00)
    );

// On reset assertion, the third memory cell remains zero.
    reset_keeps_mem2_zero: assert property (
        @(posedge clk) aclr |-> (mem[2] == 8'h00)
    );

// On reset assertion, the fourth memory cell remains zero.
    reset_keeps_mem3_zero: assert property (
        @(posedge clk) aclr |-> (mem[3] == 8'h00)
    );

// On reset deassertion, dout holds its value from the previous cycle.
    reset_release_holds_dout: assert property (
        @(posedge clk) disable iff (aclr) $fell(aclr) |-> (dout == $past(dout))
    );

// On reset deassertion, the first memory cell holds its value from the previous cycle.
    reset_release_holds_mem0: assert property (
        @(posedge clk) disable iff (aclr) $fell(aclr) |-> (mem[0] == $past(mem[0]))
    );

// On reset deassertion, the second memory cell holds its value from the previous cycle.
    reset_release_holds_mem1: assert property (
        @(posedge clk) disable iff (aclr) $fell(aclr) |-> (mem[1] == $past(mem[1]))
    );

// On reset deassertion, the third memory cell holds its value from the previous cycle.
    reset_release_holds_mem2: assert property (
        @(posedge clk) disable iff (aclr) $fell(aclr) |-> (mem[2] == $past(mem[2]))
    );

// On reset deassertion, the fourth memory cell holds its value from the previous cycle.
    reset_release_holds_mem3: assert property (
        @(posedge clk) disable iff (aclr) $fell(aclr) |-> (mem[3] == $past(mem[3]))
    );

endmodule
