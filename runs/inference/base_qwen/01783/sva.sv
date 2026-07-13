module two_bit_adder_sva (
    input logic X,
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    output logic OUT
);
    // No clock or reset signals present in the RTL

    // NAND logic check
    nand_check: assert property (
        @(posedge clk) disable iff (!RESETn) (X1 == !(A1_N & A2_N)) && (X2 == !(B1 & B2)) && (X3 == !(A1_N & B2)) && (X4 == !(A2_N & B1))
    ) else $error("NAND logic does not match expected behavior");

    // NOR logic check
    nor_check: assert property (
        @(posedge clk) disable iff (!RESETn) (OUT == !((X1 | X2)))
    ) else $error("NOR logic does not match expected behavior");

endmodule
```

**Explanation:**
- The RTL module `two_bit_adder` contains only combinational logic.
- There are no clock or reset signals present in the RTL.
- The module performs NAND operations on the inputs and then a NOR operation on the results to produce the output.
- The SVA module `two_bit_adder_sva` contains assertions to check the correctness of the NAND and NOR operations.