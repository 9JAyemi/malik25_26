module top_module_assertions (
    input logic clk,
    input logic reset,
    input logic select,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic [7:0] q,
    input logic [7:0] out_sum,
    input logic [7:0] out_comp
);

    // Reset drives the registered datapath to zero on the next cycle.
    check_reset_outputs: assert property (
        @(posedge clk)
        reset |=> (out_sum == 8'h00) && (out_comp == 8'hFF) && (q == 8'h00)
    );

    // The adder output reflects the previous cycle's captured inputs.
    check_out_sum_tracks_captured_inputs: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (out_sum == ($past(d1) + $past(d2)))
    );

    // The complement output is always the bitwise inverse of the sum output.
    check_out_comp_is_complement_of_sum: assert property (
        @(posedge clk) disable iff (reset)
        out_comp == ~out_sum
    );

    // The complement path reflects the inverse of the previous cycle's captured sum.
    check_out_comp_tracks_captured_inputs: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (out_comp == ~($past(d1) + $past(d2)))
    );

    // The mux tree always reduces to passing the sum output to q.
    check_q_equals_out_sum: assert property (
        @(posedge clk) disable iff (reset)
        q == out_sum
    );

    // The final output reflects the previous cycle's captured sum.
    check_q_tracks_captured_inputs: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (q == ($past(d1) + $past(d2)))
    );

endmodule