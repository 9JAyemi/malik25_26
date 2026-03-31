```systemverilog
module binary_counter_sva (
    input logic clk,
    input logic rst,
    output logic [3:0] count
);
    // Sequential logic for binary counter
    // Counter increments on each clock edge and resets to 0 when count reaches 15
    counter_behavior: assert property (
        @(posedge clk) disable iff (!rst) (count != 4'b1111) |-> count + 4'b1
    );
    counter_reset_behavior: assert property (
        @(posedge clk) disable iff (!rst) rst |-> count == 4'b0
    );

    // Mux behavior
    // Mux output should be count[0] when S is 0, and 0 when S is 1
    mux_behavior: assert property (
        @(posedge clk) disable iff (!rst) (mux_out == (count[0] ? 1'b0 : count[0]))
    );
endmodule
```