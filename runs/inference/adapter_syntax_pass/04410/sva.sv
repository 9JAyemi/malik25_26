module fifo_buffer_sva #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH = 4
) (
    input logic clk,
    input logic aclr,
    input logic [DATA_WIDTH-1:0] din,
    input logic [DATA_WIDTH-1:0] dout,
    input logic [DATA_WIDTH-1:0] mem [DEPTH-1:0]
);

    // Active-high asynchronous clear forces all memory locations and dout to zero.
    check_clear_state: assert property (
        @(posedge clk) aclr |-> ((mem[0] == {DATA_WIDTH{1'b0}}) &&
                                 (mem[1] == {DATA_WIDTH{1'b0}}) &&
                                 (mem[2] == {DATA_WIDTH{1'b0}}) &&
                                 (mem[3] == {DATA_WIDTH{1'b0}}) &&
                                 (dout == {DATA_WIDTH{1'b0}}))
    );

    // The first memory location captures din on each active clock.
    check_mem0_captures_din: assert property (
        @(posedge clk) disable iff (aclr)
        1'b1 |=> (mem[0] == $past(din))
    );

    // The second memory location shifts in the previous first memory location.
    check_mem1_shifts_mem0: assert property (
        @(posedge clk) disable iff (aclr)
        1'b1 |=> (mem[1] == $past(mem[0]))
    );

    // The third memory location shifts in the previous second memory location.
    check_mem2_shifts_mem1: assert property (
        @(posedge clk) disable iff (aclr)
        1'b1 |=> (mem[2] == $past(mem[1]))
    );

    // The fourth memory location shifts in the previous third memory location.
    check_mem3_shifts_mem2: assert property (
        @(posedge clk) disable iff (aclr)
        1'b1 |=> (mem[3] == $past(mem[2]))
    );

    // dout captures the previous fourth memory location.
    check_dout_captures_mem3: assert property (
        @(posedge clk) disable iff (aclr)
        1'b1 |=> (dout == $past(mem[3]))
    );

    // The full memory array and dout shift together when not in clear.
    check_full_state_shifts: assert property (
        @(posedge clk) disable iff (aclr)
        1'b1 |=> ((mem[0] == $past(mem[1])) &&
                  (mem[1] == $past(mem[2])) &&
                  (mem[2] == $past(mem[3])) &&
                  (dout == $past(mem[3])))
    );

endmodule