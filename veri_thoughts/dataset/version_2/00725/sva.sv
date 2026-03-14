module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] in,
    input logic [31:0] in2,
    input logic final_output
);
    // Mirror of RTL combinational parity path
    logic [7:0] in_xor_m;
    assign in_xor_m = ^in;
    logic parity_bit_m;
    assign parity_bit_m = in_xor_m[0] ^ in_xor_m[1] ^ in_xor_m[2] ^ in_xor_m[3] ^ in_xor_m[4] ^ in_xor_m[5] ^ in_xor_m[6] ^ in_xor_m[7];

    // Mirror of RTL counter and falling_edge logic
    logic [31:0] counter_m;
    always_ff @(posedge clk) begin
        if (reset) begin
            counter_m <= 32'd0;
        end else begin
            counter_m <= counter_m + 32'd1;
        end
    end
    logic falling_edge_m;
    assign falling_edge_m = (counter_m == 32'h7FFFFFFF);

    // Expected final output per RTL wiring
    logic expected_final_m;
    assign expected_final_m = parity_bit_m ^ falling_edge_m;

    ///// Assertions /////
    // final_output equals parity_bit ^ falling_edge (functional equivalence).
    check_final_output_function: assert property (
        @(posedge clk) disable iff (reset) final_output == expected_final_m
    );

    // When counter != 0x7FFFFFFF, final_output equals parity_bit.
    check_output_equals_parity_when_not_match: assert property (
        @(posedge clk) disable iff (reset) (counter_m != 32'h7FFFFFFF) |-> (final_output == parity_bit_m)
    );

    // When counter == 0x7FFFFFFF, final_output equals inverted parity_bit.
    check_output_equals_inverted_parity_at_match: assert property (
        @(posedge clk) disable iff (reset) (counter_m == 32'h7FFFFFFF) |-> (final_output == ~parity_bit_m)
    );

    // Output toggle equals XOR of parity toggle and falling_edge toggle.
    check_output_toggle_relation: assert property (
        @(posedge clk) disable iff (reset) ($changed(final_output)) == (($changed(parity_bit_m)) ^ ($changed(falling_edge_m)))
    );

    // Changing in2 alone (with parity and falling_edge stable) cannot change final_output.
    check_in2_irrelevant_when_others_stable: assert property (
        @(posedge clk) disable iff (reset) ($changed(in2) && $stable(parity_bit_m) && $stable(falling_edge_m)) |-> $stable(final_output)
    );

    // If neither parity nor falling_edge changes, final_output must be stable.
    check_output_stable_when_drivers_stable: assert property (
        @(posedge clk) disable iff (reset) ($stable(parity_bit_m) && $stable(falling_edge_m)) |-> $stable(final_output)
    );

    // falling_edge is high for exactly one cycle per occurrence (must deassert next cycle).
    check_falling_edge_one_cycle_pulse: assert property (
        @(posedge clk) disable iff (reset) falling_edge_m |-> ##1 !falling_edge_m
    );

    // falling_edge is zero whenever counter != 0x7FFFFFFF.
    check_falling_edge_only_when_match: assert property (
        @(posedge clk) disable iff (reset) (counter_m != 32'h7FFFFFFF) |-> (falling_edge_m == 1'b0)
    );

    // Parity monitor reduces to the simple reduction XOR of 'in'.
    check_parity_definition: assert property (
        @(posedge clk) disable iff (reset) parity_bit_m == (^in)
    );

endmodule