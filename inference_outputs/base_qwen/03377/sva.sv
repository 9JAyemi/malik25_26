```systemverilog
module hex_display_sva (
    input wire clk,
    input wire rst_n,
    input wire [3:0] in,
    input wire enable,
    output wire [6:0] out
);
    // Combinational logic: out is determined by in and enable
    // Ensure out is correctly set based on the input value and enable signal
    comb_out: assert property (
        @(posedge clk) disable iff (!rst_n) (out == (enable ? {7{in[3]}} : 7'b0000000))
    ) else $error("Combinational logic error in out calculation");

    // Ensure out is inverted if INVERT is set
    invert_out: assert property (
        @(posedge clk) disable iff (!rst_n) (out == (INVERT ? ~{7{in[3]}} : {7{in[3]}}))
    ) else $error("Inversion logic error in out calculation");

    // Ensure out is always 7'b0000000 when enable is 0
    disable_out_when_disabled: assert property (
        @(posedge clk) disable iff (!rst_n) (enable == 1'b0 |-> out == 7'b0000000)
    ) else $error("Output should be 0 when enable is 0");

endmodule
```