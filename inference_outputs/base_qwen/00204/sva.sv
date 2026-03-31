```systemverilog
module debounce_sva (
    input logic pb_debounced,
    input logic pb,
    input logic clk
);
    // Debounced output should be 0 when shift_reg is all 0s
    debounced_0: assert property (
        @(posedge clk) disable iff (!clk) (shift_reg == 4'b0000) |-> (pb_debounced == 1'b0)
    );
    // Debounced output should be 1 when shift_reg is not all 0s
    debounced_1: assert property (
        @(posedge clk) disable iff (!clk) (shift_reg != 4'b0000) |-> (pb_debounced == 1'b1)
    );
endmodule
```