```systemverilog
module binary_to_gray_sva (
    input logic [8:0] binary,
    output logic [3:0] gray
);
    // Binary to Gray conversion logic
    // gray[3] should be equal to binary[8]
    binary_to_gray_3: assert property (
        @(posedge CLK) disable iff (!RESETn) (gray[3] == binary[8])
    );
    // gray[2] should be equal to binary[8] XOR binary[7]
    binary_to_gray_2: assert property (
        @(posedge CLK) disable iff (!RESETn) (gray[2] == (binary[8] ^ binary[7]))
    );
    // gray[1] should be equal to binary[7] XOR binary[6]
    binary_to_gray_1: assert property (
        @(posedge CLK) disable iff (!RESETn) (gray[1] == (binary[7] ^ binary[6]))
    );
    // gray[0] should be equal to binary[6] XOR binary[5]
    binary_to_gray_0: assert property (
        @(posedge CLK) disable iff (!RESETn) (gray[0] == (binary[6] ^ binary[5]))
    );
endmodule
```