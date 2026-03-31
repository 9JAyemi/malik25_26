```systemverilog
module AND_32bit_sva (
    input logic clk,
    input logic rst_n,
    input logic [31:0] A,
    input logic [31:0] B,
    output logic [31:0] out
);
    // Combinational logic, but still use clocked assertions for consistency
    // Ensure that each bit of the output is the AND of the corresponding bits of A and B
    property p_and_32bit;
        @(posedge clk) disable iff (!rst_n) out == (A & B);
    endproperty

    // Assert the property
    a_and_32bit: assert property (p_and_32bit) else $error("AND operation does not match expected result");

endmodule
```