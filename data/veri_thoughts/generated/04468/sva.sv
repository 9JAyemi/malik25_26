module multiplier_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic       clk,
    input logic [7:0] PRODUCT
);

    // PRODUCT is the registered previous-cycle zero-extended truncated A+B result.
    check_product_registered_sum: assert property (
        @(posedge clk) ##1 PRODUCT == {4'h0, (($past(A) + $past(B)) & 4'hf)}
    );

    // The upper nibble of PRODUCT is always zero after the first clocked update.
    check_product_upper_nibble_zero: assert property (
        @(posedge clk) ##1 PRODUCT[7:4] == 4'h0
    );

    // The lower nibble of PRODUCT matches the previous-cycle truncated A+B value.
    check_product_lower_nibble_sum: assert property (
        @(posedge clk) ##1 PRODUCT[3:0] == (($past(A) + $past(B)) & 4'hf)
    );

endmodule