```systemverilog
module ZigbeeReceiver_sva (
    input wire carrier,
    input wire modulated,
    input wire en,
    input wire clk,
    output reg [n-1:0] out
);
    parameter n = 8; // Number of output data bits

    ///// Sequential logic behavior /////
    // When en is HIGH and carrier is HIGH, out should be set to n copies of modulated.
    // When en is LOW or carrier is LOW, out should be set to 0.
    sequential_logic: assert property (
        @(posedge clk) disable iff (!en) (carrier == 1'b1) |-> (out == {n{modulated}})
    );
    sequential_logic_reset: assert property (
        @(posedge clk) !en |-> (out == 0)
    );

endmodule
```