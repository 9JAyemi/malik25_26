module counter4_sva (
    input logic clk,
    input logic rst,
    output logic [3:0] count
);
    // Reset behavior: count should be 0 after reset
    reset: assert property (
        @(posedge clk) disable iff (!rst) count == 4'b0000
    );

    // Count should increment by 1 on each positive edge of clk, except when it reaches 9
    count_increment: assert property (
        @(posedge clk) disable iff (!rst) (count != 4'b1001) |-> count == count + 1
    );

    // Count should wrap around to 0 when it reaches 9
    count_wrap: assert property (
        @(posedge clk) disable iff (!rst) count == 4'b1001 |-> count == 4'b0000
    );
endmodule