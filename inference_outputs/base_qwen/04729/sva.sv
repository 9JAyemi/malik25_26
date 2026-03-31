```systemverilog
module binary_to_gray_sva (
    input logic clk,
    input logic [3:0] binary_in,
    output logic [3:0] gray_out
);
    // Binary to Gray conversion logic must be applied on the rising edge of the clock.
    binary_to_gray_conversion: assert property (
        @(posedge clk) $stable(binary_in) |-> (gray_out[3] == binary_in[3]) && 
        (gray_out[2] == binary_in[3] ^ binary_in[2]) && 
        (gray_out[1] == binary_in[2] ^ binary_in[1]) && 
        (gray_out[0] == binary_in[1] ^ binary_in[0])
    );
endmodule
```