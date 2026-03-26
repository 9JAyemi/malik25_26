module top_module_sva (
    input logic        clk,
    input logic [3:0]  in1,
    input logic [3:0]  in2,
    input logic        select,
    input logic [3:0]  out
);

    // Output matches the exact RTL mux-and expression.
    check_rtl_function: assert property (
        @(posedge clk) out === ((select == 1'b0) ? (in1 & in2) : in1)
    );

    // When select is low, out is the bitwise AND of in1 and in2.
    check_select_low_and: assert property (
        @(posedge clk) (select === 1'b0) |-> (out === (in1 & in2))
    );

    // When select is high, out passes through in1.
    check_select_high_passthrough: assert property (
        @(posedge clk) (select === 1'b1) |-> (out === in1)
    );

    // A zero in1 forces out to zero on either data path.
    check_zero_in1_zero_out: assert property (
        @(posedge clk) (in1 === 4'b0000) |-> (out === 4'b0000)
    );

    // All ones on in2 makes the AND path equal in1.
    check_all_ones_in2_passthrough: assert property (
        @(posedge clk) (in2 === 4'b1111) |-> (out === in1)
    );

    // With select low and in1 all ones, out equals in2.
    check_select_low_all_ones_in1: assert property (
        @(posedge clk) ((select === 1'b0) && (in1 === 4'b1111)) |-> (out === in2)
    );

endmodule