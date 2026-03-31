```systemverilog
module bin2gray_sva (
    input wire [3:0] bin,
    output reg [3:0] gray
);
    // No clock or reset signals in this combinational logic module

    // Property to check that the gray output is correctly calculated based on the bin input
    property p_gray_calculation;
        @(posedge CLK) disable iff (!RESETn) (gray[3] == bin[3]) && (gray[2] == bin[3] ^ bin[2]) && (gray[1] == bin[2] ^ bin[1]) && (gray[0] == bin[1] ^ bin[0]);
    endproperty

    // Assert the property to ensure the gray output is correct
    a_gray_calculation: assert property (p_gray_calculation) else $error("Gray output calculation is incorrect");
endmodule
```