```systemverilog
module xor_inv_multiplexer_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic sel_b1,
    input logic sel_b2,
    input logic sel_out,
    output logic out_always,
    output logic [3:0] out_xor,
    output logic [3:0] out_xor_inv,
    output logic out_logical_inv
);
    // 2-to-1 multiplexer to select between a and b
    // selected_input_b1 can only be a or b
    selected_input_b1: assert property (
        @(posedge clk) disable iff (!clk) (sel_b1 == 1'b0) |-> (selected_input_b1 == a)
    );
    selected_input_b1: assert property (
        @(posedge clk) disable iff (!clk) (sel_b1 == 1'b1) |-> (selected_input_b1 == b)
    );

    // 2-to-1 multiplexer to select between selected_input_b1 and b
    // selected_input_b2 can only be a, b, or selected_input_b1
    selected_input_b2: assert property (
        @(posedge clk) disable iff (!clk) (sel_b2 == 1'b0) |-> (selected_input_b2 == selected_input_b1)
    );
    selected_input_b2: assert property (
        @(posedge clk) disable iff (!clk) (sel_b2 == 1'b1) |-> (selected_input_b2 == b)
    );

    // XOR and inverter operations on the selected input
    // out_xor can only be a XOR selected_input_b2
    out_xor: assert property (
        @(posedge clk) disable iff (!clk) (out_xor == (selected_input_b2 ^ a))
    );

    // out_xor_inv can only be the inverse of out_xor
    out_xor_inv: assert property (
        @(posedge clk) disable iff (!clk) (out_xor_inv == ~out_xor)
    );

    // out_logical_inv can only be the logical inverse of out_xor
    out_logical_inv: assert property (
        @(posedge clk) disable iff (!clk) (out_logical_inv == !out_xor)
    );

    // 2-to-1 multiplexer to select between XOR and logical inverse outputs
    // out_always can only be out_xor_inv or out_logical_inv
    out_always: assert property (
        @(posedge clk) disable iff (!clk) (sel_out == 1'b0) |-> (out_always == out_logical_inv)
    );
    out_always: assert property (
        @(posedge clk) disable iff (!clk) (sel_out == 1'b1) |-> (out_always == out_xor_inv)
    );
endmodule
```