module nand2_module_sva (
    input logic in1,
    input logic in2,
    input logic clk,
    input logic out
);

    // Output is the registered NAND of the prior cycle's inputs.
    check_registered_nand: assert property (
        @(posedge clk) 1'b1 |=> (out == ~(in1 & in2))
    );

    // A high output means the prior cycle's inputs were not both high.
    check_out_high_implies_inputs_not_both_high: assert property (
        @(posedge clk) 1'b1 |=> ((out == 1'b1) -> ((in1 == 1'b0) || (in2 == 1'b0)))
    );

    // A low output means the prior cycle's inputs were both high.
    check_out_low_implies_inputs_both_high: assert property (
        @(posedge clk) 1'b1 |=> ((out == 1'b0) -> ((in1 == 1'b1) && (in2 == 1'b1)))
    );

endmodule