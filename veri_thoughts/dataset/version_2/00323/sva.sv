module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] result,
    input logic [1:0]  sub_out,
    input logic        mux_out,
    input logic [31:0] final_out
);

    // subtractor bit 0 is the XOR of a[0] and b[0].
    check_sub_out_bit0: assert property (
        @(posedge clk) sub_out[0] == (a[0] ^ b[0])
    );

    // subtractor bit 1 includes the carry generated from bit 0.
    check_sub_out_bit1: assert property (
        @(posedge clk) sub_out[1] == (a[1] ^ b[1] ^ (a[0] & b[0]))
    );

    // mux_out matches the instantiated mux logic on a[0], b[0], a[1], and b[1].
    check_mux_out_logic: assert property (
        @(posedge clk)
        mux_out == ((a[0] & ~b[0] & ~a[1] & ~b[1]) | (~a[0] & b[0] & ~a[1] & ~b[1]))
    );

    // final_out is the zero-extended XOR of a[0] and b[0] when select is high.
    check_final_out_when_select: assert property (
        @(posedge clk)
        select |-> (final_out == {31'b0, (a[0] ^ b[0])})
    );

    // final_out is the zero-extended sub_out value when select is low.
    check_final_out_when_not_select: assert property (
        @(posedge clk)
        !select |-> (final_out == {30'b0, sub_out})
    );

    // result follows the top-level select between mux_out and final_out.
    check_result_top_muxing: assert property (
        @(posedge clk)
        result == (select ? {31'b0, mux_out} : final_out)
    );

    // result matches the mux path expression when select is high.
    check_result_mux_path_exact: assert property (
        @(posedge clk)
        select |-> (result == {31'b0, ((a[0] & ~b[0] & ~a[1] & ~b[1]) | (~a[0] & b[0] & ~a[1] & ~b[1]))})
    );

    // result matches the low two sum bits when select is low.
    check_result_subtractor_path_exact: assert property (
        @(posedge clk)
        !select |-> (result == {30'b0, (a[1] ^ b[1] ^ (a[0] & b[0])), (a[0] ^ b[0])})
    );

endmodule