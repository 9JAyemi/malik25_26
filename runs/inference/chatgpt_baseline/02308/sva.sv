module nand2_module_sva (
    input logic clk,
    input logic in1,
    input logic in2,
    input logic out
);
    // Clock: clk; no reset present in RTL. Sequential logic: out is a 1-cycle registered NAND of in1 & in2.

    // Output equals NAND of inputs sampled on previous cycle.
    check_registered_nand: assert property (
        @(posedge clk) out == ~( $past(in1) & $past(in2) )
    );

    // Truth table: prev(in1,in2)=00 -> out=1.
    check_truth_00: assert property (
        @(posedge clk) ($past(in1)==1'b0 && $past(in2)==1'b0) |-> (out==1'b1)
    );

    // Truth table: prev(in1,in2)=01 -> out=1.
    check_truth_01: assert property (
        @(posedge clk) ($past(in1)==1'b0 && $past(in2)==1'b1) |-> (out==1'b1)
    );

    // Truth table: prev(in1,in2)=10 -> out=1.
    check_truth_10: assert property (
        @(posedge clk) ($past(in1)==1'b1 && $past(in2)==1'b0) |-> (out==1'b1)
    );

    // Truth table: prev(in1,in2)=11 -> out=0.
    check_truth_11: assert property (
        @(posedge clk) ($past(in1)==1'b1 && $past(in2)==1'b1) |-> (out==1'b0)
    );

    // If the input pair at t-1 equals the pair at t-2, then out must equal its previous value.
    check_output_stable_when_inputs_repeat: assert property (
        @(posedge clk) ($past(in1)==$past(in1,2) && $past(in2)==$past(in2,2)) |-> (out==$past(out))
    );

    // If the NAND of inputs at t-1 differs from that at t-2, out must differ from its previous value.
    check_output_changes_when_function_changes: assert property (
        @(posedge clk) ( ~( $past(in1) & $past(in2) ) != ~( $past(in1,2) & $past(in2,2) ) ) |-> (out != $past(out))
    );
endmodule