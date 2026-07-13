module four_to_one_mux_sva (
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    output logic out
);
    // Sequential logic is not present, so all assertions will be clocked.
    // No reset signal is present, so no disable iff clause is needed.

    // Mux output should match the selected input
    mux_output: assert property (
        @(posedge clk) $rose(sel) |-> (out == (sel == 2'b00 ? in0 : (sel == 2'b01 ? in1 : (sel == 2'b10 ? in2 : in3))))
    ) else $error("Mux output does not match selected input");

    // Mux output should not change when sel does not change
    mux_stable: assert property (
        @(posedge clk) $stable(sel) |-> $stable(out)
    ) else $error("Mux output changes when sel does not change");

    // Mux output should be one of the inputs
    mux_valid_output: assert property (
        @(posedge clk) $rose(sel) |-> (out == in0 || out == in1 || out == in2 || out == in3)
    ) else $error("Mux output is not one of the inputs");

endmodule