module top_module_sva(
    input logic clk,
    input logic a,
    input logic b,
    input logic sel_b1,
    input logic sel_b2,
    input logic out_always
);

wire and_out;
wire mux_out;
wire final_out;

assign and_out  = a & b;
assign mux_out  = (sel_b1 & sel_b2) ? b : a;
assign final_out = and_out ^ mux_out;

// Output must match the combinational result of the submodules.
check_output_matches_final_out: assert property (
    @(posedge clk) out_always == final_out
);

// When both select bits are high, the mux path uses b.
check_output_when_b_selected: assert property (
    @(posedge clk) (sel_b1 & sel_b2) |-> (out_always == ((a & b) ^ b))
);

// When either select bit is low, the mux path uses a.
check_output_when_a_selected: assert property (
    @(posedge clk) !(sel_b1 & sel_b2) |-> (out_always == ((a & b) ^ a))
);

// With b selected, the final function simplifies to ~a & b.
check_selected_b_simplified: assert property (
    @(posedge clk) (sel_b1 & sel_b2) |-> (out_always == (~a & b))
);

// With a selected, the final function simplifies to a & ~b.
check_selected_a_simplified: assert property (
    @(posedge clk) !(sel_b1 & sel_b2) |-> (out_always == (a & ~b))
);

// Equal data inputs always force the XOR result low.
check_equal_inputs_drive_zero: assert property (
    @(posedge clk) (a == b) |-> (out_always == 1'b0)
);

// A high output is only possible when a and b differ.
check_high_output_requires_mismatch: assert property (
    @(posedge clk) out_always |-> (a ^ b)
);

// For a=1 and b=0, the output is high only when a is selected.
check_case_a1_b0: assert property (
    @(posedge clk) (a & ~b) |-> (out_always == !(sel_b1 & sel_b2))
);

// For a=0 and b=1, the output is high only when b is selected.
check_case_a0_b1: assert property (
    @(posedge clk) (~a & b) |-> (out_always == (sel_b1 & sel_b2))
);

endmodule