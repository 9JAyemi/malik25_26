module binary_multiplier_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] result
);
    // The logic is purely combinational as there are no clock signals or reset.
    // The result is directly assigned based on the multiplication of a and b.
    
    // Check that the result is correct for the given inputs.
    check_result: assert property (
        @(posedge clk) disable iff (!RESETn) (result == {8'b0, a} * {8'b0, b})
    );
endmodule