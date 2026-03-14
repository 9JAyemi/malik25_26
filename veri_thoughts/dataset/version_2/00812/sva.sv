module max_module_sva (
    input logic clk,
    input logic [3:0] priority_enc_out,
    input logic [3:0] comb_circuit_out,
    input logic [3:0] max_out
);
    // Output equals the max of the two inputs (unsigned compare).
    check_max_function: assert property (
        @(posedge clk) max_out == (priority_enc_out > comb_circuit_out ? priority_enc_out : comb_circuit_out)
    );

    // Output is always equal to one of the two inputs.
    check_output_is_one_of_inputs: assert property (
        @(posedge clk) (max_out == priority_enc_out) || (max_out == comb_circuit_out)
    );

    // When priority_enc_out > comb_circuit_out, select priority_enc_out.
    check_select_priority_when_greater: assert property (
        @(posedge clk) (priority_enc_out > comb_circuit_out) |-> (max_out == priority_enc_out)
    );

    // When priority_enc_out <= comb_circuit_out, select comb_circuit_out.
    check_select_comb_when_not_greater: assert property (
        @(posedge clk) (priority_enc_out <= comb_circuit_out) |-> (max_out == comb_circuit_out)
    );

    // On tie, output equals comb_circuit_out.
    check_tie_selects_comb: assert property (
        @(posedge clk) (priority_enc_out == comb_circuit_out) |-> (max_out == comb_circuit_out)
    );

    // Output is not less than priority_enc_out.
    check_max_ge_priority: assert property (
        @(posedge clk) max_out >= priority_enc_out
    );

    // Output is not less than comb_circuit_out.
    check_max_ge_comb: assert property (
        @(posedge clk) max_out >= comb_circuit_out
    );

    // If both inputs are stable between cycles, output is stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) ($stable(priority_enc_out) && $stable(comb_circuit_out)) |-> $stable(max_out)
    );

    // If output equals priority_enc_out, then priority_enc_out > comb_circuit_out.
    check_out_eq_priority_implies_priority_greater: assert property (
        @(posedge clk) (max_out == priority_enc_out) |-> (priority_enc_out > comb_circuit_out)
    );

    // If output equals comb_circuit_out, then comb_circuit_out >= priority_enc_out.
    check_out_eq_comb_implies_comb_ge_priority: assert property (
        @(posedge clk) (max_out == comb_circuit_out) |-> (comb_circuit_out >= priority_enc_out)
    );
endmodule