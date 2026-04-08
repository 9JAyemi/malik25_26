module top_module_sva(
    input logic clk,
    input logic reset,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic select,
    input logic [7:0] out
);

    wire [7:0] and_out;
    wire [7:0] xor_out;

    assign and_out = in1 & in2;
    assign xor_out = and_out ^ in2;

    // Output must always match the selected data path.
    check_final_output_function: assert property (
        @(posedge clk) disable iff (reset)
        out == (select ? xor_out : and_out)
    );

    // When select is low, output must be the AND result.
    check_and_path_selected: assert property (
        @(posedge clk) disable iff (reset)
        !select |-> (out == and_out)
    );

    // When select is high, output must be the XOR result.
    check_xor_path_selected: assert property (
        @(posedge clk) disable iff (reset)
        select |-> (out == xor_out)
    );

    // A zero in2 forces both paths to zero.
    check_zero_in2_forces_zero_out: assert property (
        @(posedge clk) disable iff (reset)
        (in2 == 8'h00) |-> (out == 8'h00)
    );

    // Output bits can only be set where in2 has set bits.
    check_out_subset_of_in2: assert property (
        @(posedge clk) disable iff (reset)
        ((out & ~in2) == 8'h00)
    );

    // On the XOR-selected path, output cannot overlap asserted bits in in1.
    check_xor_path_disjoint_from_in1: assert property (
        @(posedge clk) disable iff (reset)
        select |-> ((out & in1) == 8'h00)
    );

    // If sampled inputs and select are unchanged, sampled output must be unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset)
        $stable({in1, in2, select}) |-> $stable(out)
    );

    // With all ones on in1, the AND-selected path passes through in2.
    check_and_path_passthrough_when_in1_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        (!select && (in1 == 8'hFF)) |-> (out == in2)
    );

    // With all ones on in1, the XOR-selected path must be zero.
    check_xor_path_zero_when_in1_all_ones: assert property (
        @(posedge clk) disable iff (reset)
        (select && (in1 == 8'hFF)) |-> (out == 8'h00)
    );

    // With zero on in1, the XOR-selected path passes through in2.
    check_xor_path_passthrough_when_in1_zero: assert property (
        @(posedge clk) disable iff (reset)
        (select && (in1 == 8'h00)) |-> (out == in2)
    );

endmodule