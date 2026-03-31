```systemverilog
module shift_register_assertions (
    input logic clk,
    input logic d,
    output logic q
);
    // Shift register behavior: q should always be the least significant bit of reg_data
    shift_register_property: assert property (
        @(posedge clk) disable iff (!clk) q == reg_data[0]
    );
endmodule
```