module top_module_sva (
    input logic [99:0] in,
    input logic out_and,
    input logic out_or,
    input logic out_xor
);
    // Sequential logic is not present in this RTL, so all logic is combinational.
    // Therefore, we will use clocked assertions (@(posedge clk)) for all properties.

    // Check that out_and is the result of the AND operation on in
    and_result: assert property (
        @(posedge clk) disable iff (!reset_n) out_and == &in
    ) else $error("out_and is not the result of the AND operation on in");

    // Check that out_or is the result of the OR operation on in
    or_result: assert property (
        @(posedge clk) disable iff (!reset_n) out_or == |in
    ) else $error("out_or is not the result of the OR operation on in");

    // Check that out_xor is the result of the XOR operation on in
    xor_result: assert property (
        @(posedge clk) disable iff (!reset_n) out_xor == ^in
    ) else $error("out_xor is not the result of the XOR operation on in");
endmodule
```

### Explanation:
- **Clock and Reset**: The RTL does not include any clock or reset signals, so the assertions are combinational.
- **Logic Type**: The logic in the RTL is purely combinational.
- **Key Signals**: The key signals are `in`, `out_and`, `out_or`, and `out_xor`.
- **Functional Behaviors**: The module performs AND, OR, and XOR operations on the input `in` and outputs the results `out_and`, `out_or`, and `out_xor`.

### Assertions:
- `and_result`: Ensures that `out_and` is the result of the AND operation on `in`.
- `or_result`: Ensures that `out_or` is the result of the OR operation on `in`.
- `xor_result`: Ensures that `out_xor` is the result of the XOR operation on `in`.

These assertions are clocked using `@(posedge clk)` and disabled during reset (`disable iff (!reset_n)`), ensuring they only check the logic when the design is not in reset.