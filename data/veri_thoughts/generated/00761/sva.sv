module comparator_sva (
    input logic clk,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [1:0] out
);
    ///// Combinational mapping checks /////
    // When in1 equals in2, out must be 2'b00.
    map_eq: assert property (
        @(posedge clk) (in1 == in2) |-> (out == 2'b00)
    );
    // When in1 is greater than in2, out must be 2'b01.
    map_gt: assert property (
        @(posedge clk) (in1 > in2) |-> (out == 2'b01)
    );
    // When in1 is less than in2, out must be 2'b10.
    map_lt: assert property (
        @(posedge clk) (in1 < in2) |-> (out == 2'b10)
    );

    ///// Reverse mapping (code implies relation) /////
    // If out is 2'b00, inputs must be equal.
    rev_map_eq: assert property (
        @(posedge clk) (out == 2'b00) |-> (in1 == in2)
    );
    // If out is 2'b01, in1 must be greater than in2.
    rev_map_gt: assert property (
        @(posedge clk) (out == 2'b01) |-> (in1 > in2)
    );
    // If out is 2'b10, in1 must be less than in2.
    rev_map_lt: assert property (
        @(posedge clk) (out == 2'b10) |-> (in1 < in2)
    );

    ///// Encoding sanity /////
    // out must never be 2'b11.
    out_never_illegal_11: assert property (
        @(posedge clk) out != 2'b11
    );

    ///// Stability relationships /////
    // If inputs are stable across a cycle, out must be stable.
    output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(in1) && $stable(in2)) |-> $stable(out)
    );
    // If out changes, at least one input must have changed.
    out_change_requires_input_change: assert property (
        @(posedge clk) $changed(out) |-> ($changed(in1) || $changed(in2))
    );
endmodule