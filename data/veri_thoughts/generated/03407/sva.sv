module top_module_sva (
    input logic clk,
    input logic reset,
    input logic select,
    input logic [2:0] vec,
    input logic [2:0] outv,
    input logic o2,
    input logic o1,
    input logic o0
);

    // outv must implement the select-controlled mux on vec.
    check_outv_mux_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (outv == (select ? vec : 3'b000))
    );

    // o2 must be vec[2] when selected, else 0.
    check_o2_mux_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (o2 == (select ? vec[2] : 1'b0))
    );

    // o1 must be vec[1] when selected, else 0.
    check_o1_mux_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (o1 == (select ? vec[1] : 1'b0))
    );

    // o0 must be vec[0] when selected, else 0.
    check_o0_mux_function: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (o0 == (select ? vec[0] : 1'b0))
    );

    // outv must always match the concatenation of o2, o1, and o0.
    check_outv_matches_split_outputs: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |-> (outv == {o2, o1, o0})
    );

endmodule