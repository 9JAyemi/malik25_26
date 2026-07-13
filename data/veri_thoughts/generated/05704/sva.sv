module top_module_sva (
    input logic        clk,
    input logic        reset,
    input logic [31:0] in,
    input logic        select,
    input logic        q,
    input logic [31:0] out_module1,
    input logic        q_module2,
    input logic [31:0] out_functional
);

    // module1 output clears on the cycle after reset is asserted.
    check_module1_reset_clears: assert property (
        @(posedge clk) reset |=> (out_module1 == 32'b0)
    );

    // module1 shifts prior bits [30:0] into bits [31:1].
    check_module1_shift_upper_bits: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out_module1[31:1] == $past(out_module1[30:0]))
    );

    // module1 loads the previous in[31] into bit 0.
    check_module1_loads_input_into_lsb: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (out_module1[0] == $past(in[31]))
    );

    // module2 registers the previous out_module1[0].
    check_module2_captures_module1_lsb: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (q_module2 == $past(out_module1[0]))
    );

    // functional_module passes out_module1 when select is high.
    check_functional_select_high: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (out_functional == out_module1)
    );

    // functional_module zero-extends q_module2 when select is low.
    check_functional_select_low: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (out_functional == {31'b0, q_module2})
    );

    // top-level q is the low bit of out_functional.
    check_top_q_matches_out_functional_lsb: assert property (
        @(posedge clk) disable iff (reset)
        q == out_functional[0]
    );

    // q matches out_module1[0] when select is high.
    check_top_q_select_high: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (q == out_module1[0])
    );

    // q matches q_module2 when select is low.
    check_top_q_select_low: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (q == q_module2)
    );

endmodule

bind top_module top_module_sva top_module_sva_inst (
    .clk(clk),
    .reset(reset),
    .in(in),
    .select(select),
    .q(q),
    .out_module1(out_module1),
    .q_module2(q_module2),
    .out_functional(out_functional)
);