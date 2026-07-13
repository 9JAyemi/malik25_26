module clock_gate_en_sva (
    input logic clk,
    input logic en,
    input logic data_in,
    input logic data_out
);
    ///// Clock gating logic /////
    // data_out should only change when en is HIGH.
    clock_gating_1: assert property (
        @(posedge clk) disable iff (!clk) $changed(data_out) |-> en == 1'b1
    );
    // data_out should be LOW when en is LOW.
    clock_gating_2: assert property (
        @(posedge clk) disable iff (!clk) (en == 1'b0) |-> data_out == 1'b0
    );
endmodule