module binary_counter_sva (
    input logic clk,
    input logic rst,
    output logic [2:0] count
);
    // Reset behavior: count should be 0 at reset
    reset: assert property (
        @(posedge clk) disable iff (!rst) count == 3'b0
    );

    // Counting behavior: count should increment by 1 on each clock cycle
    counting: assert property (
        @(posedge clk) disable iff (!rst) count == count + 1
    );
endmodule