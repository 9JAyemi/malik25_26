module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [31:0] in,
    output logic [31:0] out
);

    // Rising edge detection logic
    // out is high only when there is a rising edge in in
    rising_edge_detection: assert property (
        @(posedge clk) disable iff (!reset) (out == 1'b1) |-> (in == 1'b1) && (prev_state == 1'b0)
    );

    // Reset behavior
    // At reset, out should be low
    reset_behavior: assert property (
        @(posedge clk) disable iff (!reset) reset |-> (out == 1'b0)
    );

endmodule