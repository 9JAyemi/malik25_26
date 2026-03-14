module top_module_sva (
    input logic clk,
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [7:0] in3,
    input logic [7:0] out_xor,
    input logic [7:0] out_and,
    input logic [7:0] out_final
);
    // out_xor equals bitwise XOR of in1 and in2.
    check_out_xor_computation: assert property (
        @(posedge clk) out_xor == (in1 ^ in2)
    );

    // out_and equals bitwise AND of in1, in2, and in3.
    check_out_and_computation: assert property (
        @(posedge clk) out_and == (in1 & in2 & in3)
    );

    // out_final updates to prior-cycle (out_xor + out_and).
    check_out_final_pipeline_from_internal: assert property (
        @(posedge clk) 1'b1 |=> (out_final == $past(out_xor + out_and))
    );

    // out_final updates to prior-cycle ((in1 ^ in2) + (in1 & in2 & in3)).
    check_out_final_pipeline_from_inputs: assert property (
        @(posedge clk) 1'b1 |=> (out_final == $past((in1 ^ in2) + (in1 & in2 & in3)))
    );

    // If in1 and in2 are stable over a cycle, out_xor is stable over that cycle.
    check_out_xor_stable_if_inputs_stable: assert property (
        @(posedge clk) ($stable(in1) && $stable(in2)) |-> $stable(out_xor)
    );

    // If in1, in2, and in3 are stable over a cycle, out_and is stable over that cycle.
    check_out_and_stable_if_inputs_stable: assert property (
        @(posedge clk) ($stable(in1) && $stable(in2) && $stable(in3)) |-> $stable(out_and)
    );

    // If out_xor and out_and are stable, out_final remains stable on the next cycle.
    check_out_final_stable_if_internal_stable: assert property (
        @(posedge clk) ($stable(out_xor) && $stable(out_and)) |=> $stable(out_final)
    );

    // out_and only has 1s where all inputs have 1s.
    check_out_and_subset_of_inputs: assert property (
        @(posedge clk) ((out_and & ~in1) == 8'h00) && ((out_and & ~in2) == 8'h00) && ((out_and & ~in3) == 8'h00)
    );

    // A change in (out_xor+out_and) causes a change in out_final one cycle later.
    check_out_final_reflects_sum_change: assert property (
        @(posedge clk) ((out_xor + out_and) != $past(out_xor + out_and)) |=> (out_final != $past(out_final))
    );

    // If out_xor and out_and are zero, out_final becomes zero next cycle.
    check_out_final_zero_propagation: assert property (
        @(posedge clk) ((out_xor == 8'h00) && (out_and == 8'h00)) |=> (out_final == 8'h00)
    );
endmodule