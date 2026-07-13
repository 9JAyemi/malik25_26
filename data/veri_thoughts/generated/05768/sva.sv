module mux_2to1_enable_sva (
    input logic clk,
    input logic enable,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] out
);

    // DUT is combinational; clk is only used to sample assertions and there is no reset.

    // When enable is 0, out must select in1.
    check_select_in1: assert property (
        @(posedge clk) (enable === 1'b0) |-> (out === in1)
    );

    // When enable is not 0, out must select in2.
    check_select_in2: assert property (
        @(posedge clk) (enable !== 1'b0) |-> (out === in2)
    );

    // The output must always match the implemented mux branch.
    check_mux_function: assert property (
        @(posedge clk)
        (((enable === 1'b0) && (out === in1)) ||
         ((enable !== 1'b0) && (out === in2)))
    );

    // With the in1 path selected and unchanged, out stays unchanged.
    check_stable_in1_path: assert property (
        @(posedge clk) (enable === 1'b0 && $stable(enable) && $stable(in1)) |-> $stable(out)
    );

    // With the in2 path selected and unchanged, out stays unchanged.
    check_stable_in2_path: assert property (
        @(posedge clk) (enable !== 1'b0 && $stable(enable) && $stable(in2)) |-> $stable(out)
    );

endmodule