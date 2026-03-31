```systemverilog
module mux_2to1_sva (
    input logic a,
    input logic b,
    input logic sel,
    output logic out
);
    // Sequential logic is not present, so we use @(posedge clk) for assertions.
    // The logic is purely combinational, so we clock our assertions to the appropriate edge.

    // Mux output should be either a or b based on the sel signal.
    mux_output_correct: assert property (
        @(posedge clk) disable iff (!resetn) (sel == 1'b1) |-> (out == b)
    ) else $error("Mux output should be b when sel is 1'b1");

    mux_output_correct_2: assert property (
        @(posedge clk) disable iff (!resetn) (sel == 1'b0) |-> (out == a)
    ) else $error("Mux output should be a when sel is 1'b0");

    // Mux output should not be undefined when sel is not 1'b0 or 1'b1.
    mux_output_undefined: assert property (
        @(posedge clk) disable iff (!resetn) (sel != 1'b0 && sel != 1'b1) |-> (out == 1'bx)
    ) else $error("Mux output should be undefined when sel is not 1'b0 or 1'b1");

    // Reset behavior: out should be undefined on reset.
    reset_out_undefined: assert property (
        @(posedge clk) !resetn |-> (out == 1'bx)
    ) else $error("Mux output should be undefined on reset");

endmodule
```