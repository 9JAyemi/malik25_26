module four_bit_counter_sva (
    input logic clk,
    input logic reset,
    output logic [3:0] count
);
    // Reset behavior: count should be 0 at reset
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'b0)
    );

    // Counting behavior: count should increment by 1 on each clock edge
    counting_behavior: assert property (
        @(posedge clk) disable iff (!reset) (count == 4'b1111) |-> count == 4'b0000
    );
endmodule