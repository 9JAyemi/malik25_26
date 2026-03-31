```systemverilog
module BCD_to_Binary_sva (
    input logic [3:0] bcd_in,
    output logic [7:0] bin_out
);
    // BCD to Binary conversion logic
    // bin_out should be updated based on the value of bcd_in
    bcd_to_binary: assert property (
        @(posedge clk) disable iff (!RESETn) (bin_out == {bcd_in, 4'b0000})
    ) else $error("BCD to Binary conversion error");
endmodule
```