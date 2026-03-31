module nand2_module_sva (
    input logic in1,
    input logic in2,
    input logic clk,
    input logic out
);

// Output is the registered NAND of the two inputs.
    check_registered_nand_function: assert property (
        @(posedge clk) 1'b1 |=> (out == ~(in1 & in2))
    );

// A high-high input pair drives the registered output low.
    check_high_high_drives_low: assert property (
        @(posedge clk) (in1 == 1'b1 && in2 == 1'b1) |=> (out == 1'b0)
    );

// Any low input forces the registered output high.
    check_any_low_drives_high: assert property (
        @(posedge clk) (in1 == 1'b0 || in2 == 1'b0) |=> (out == 1'b1)
    );

// A low output requires both inputs to be high.
    check_low_output_requires_both_high: assert property (
        @(posedge clk) (out == 1'b0) |=> (in1 == 1'b1 && in2 == 1'b1)
    );

// A high output requires at least one input to be low.
    check_high_output_requires_any_low: assert property (
        @(posedge clk) (out == 1'b1) |=> (in1 == 1'b0 || in2 == 1'b0)
    );

endmodule
