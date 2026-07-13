module data_buffer_sva (
    input logic [31:0] data_in,
    input logic [6:0]  ecc_in,
    input logic        tag_in,
    input logic        valid_in,
    input logic        control_tag_in,
    input logic        error_in,
    input logic        dequeue_in,
    input logic        por_req_in,
    input logic        clk,
    input logic        reset,
    input logic [31:0] data_out,
    input logic [6:0]  ecc_out,
    input logic        tag_out,
    input logic        valid_out,
    input logic        control_tag_out,
    input logic        error_out,
    input logic        dequeue_out,
    input logic        por_req_out
);
    // Reset drives outputs to known values.
    reset_values: assert property (
        @(posedge clk) reset |-> (data_out == 32'd0) && (ecc_out == 7'd0) && (tag_out == 1'b0) &&
                                 (valid_out == 1'b0) && (control_tag_out == 1'b0) &&
                                 (error_out == 1'b0) && (dequeue_out == 1'b0) &&
                                 (por_req_out == 1'b1)
    );

    // POR request clears por_req_out.
    por_req_clears_on_input: assert property (
        @(posedge clk) disable iff (reset) por_req_in |-> (por_req_out == 1'b0)
    );

    // por_req_out can only fall when por_req_in is asserted.
    por_req_only_falls_on_input: assert property (
        @(posedge clk) disable iff (reset) $fell(por_req_out) |-> por_req_in
    );

    // por_req_out can only rise when reset is asserted.
    por_req_rise_only_on_reset: assert property (
        @(posedge clk) $rose(por_req_out) |-> reset
    );

    // control_tag_in sets control_tag_out.
    control_tag_set_on_input: assert property (
        @(posedge clk) disable iff (reset) control_tag_in |-> (control_tag_out == 1'b1)
    );

    // dequeue_in (without control_tag_in) clears control_tag_out.
    control_tag_clear_on_dequeue_only: assert property (
        @(posedge clk) disable iff (reset) (!control_tag_in && dequeue_in) |-> (control_tag_out == 1'b0)
    );

    // control_tag_in has priority over dequeue_in when both asserted.
    control_tag_priority_over_dequeue: assert property (
        @(posedge clk) disable iff (reset) (control_tag_in && dequeue_in) |-> (control_tag_out == 1'b1)
    );

    // control_tag_out falls only when cleared by dequeue_in with no control_tag_in.
    control_tag_fall_requires_dequeue: assert property (
        @(posedge clk) disable iff (reset) $fell(control_tag_out) |-> (!control_tag_in && dequeue_in)
    );

    // control_tag_out holds when neither control_tag_in nor dequeue_in is asserted.
    control_tag_stable_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!control_tag_in && !dequeue_in) |-> $stable(control_tag_out)
    );

    // On valid_in, capture data/ecc/tag to outputs.
    capture_data_on_valid: assert property (
        @(posedge clk) disable iff (reset) valid_in |-> (data_out == data_in) && (ecc_out == ecc_in) && (tag_out == tag_in)
    );

    // valid_out is set when valid_in without dequeue_in.
    valid_sets_on_valid_no_dequeue: assert property (
        @(posedge clk) disable iff (reset) (valid_in && !dequeue_in) |-> (valid_out == 1'b1)
    );

    // dequeue_in clears valid_out.
    valid_cleared_on_dequeue: assert property (
        @(posedge clk) disable iff (reset) dequeue_in |-> (valid_out == 1'b0)
    );

    // valid_out can only rise when valid_in and not dequeue_in.
    valid_rise_requires_valid_not_dequeue: assert property (
        @(posedge clk) disable iff (reset) $rose(valid_out) |-> (valid_in && !dequeue_in)
    );

    // valid_out can only fall when dequeue_in is asserted.
    valid_fall_requires_dequeue: assert property (
        @(posedge clk) disable iff (reset) $fell(valid_out) |-> dequeue_in
    );

    // When idle w.r.t. valid/dequeue, valid_out holds.
    valid_stable_when_idle: assert property (
        @(posedge clk) disable iff (reset) (!valid_in && !dequeue_in) |-> $stable(valid_out)
    );

    // Data/ECC/tag hold when valid_in is not asserted.
    data_ecc_tag_stable_without_valid: assert property (
        @(posedge clk) disable iff (reset) !valid_in |-> ($stable(data_out) && $stable(ecc_out) && $stable(tag_out))
    );

    // dequeue_in sets dequeue_out.
    dequeue_flag_set_on_input: assert property (
        @(posedge clk) disable iff (reset) dequeue_in |-> (dequeue_out == 1'b1)
    );

    // dequeue_out can only rise when dequeue_in is asserted.
    dequeue_flag_only_rises_on_input: assert property (
        @(posedge clk) disable iff (reset) $rose(dequeue_out) |-> dequeue_in
    );

    // dequeue_out never falls without reset.
    dequeue_flag_never_falls_without_reset: assert property (
        @(posedge clk) disable iff (reset) !$fell(dequeue_out)
    );

    // error_in sets error_out (sticky until reset).
    error_set_on_input: assert property (
        @(posedge clk) disable iff (reset) error_in |-> (error_out == 1'b1)
    );

    // error_out can only rise when error_in is asserted.
    error_only_rises_on_error: assert property (
        @(posedge clk) disable iff (reset) $rose(error_out) |-> error_in
    );

    // error_out never falls without reset.
    error_never_falls_without_reset: assert property (
        @(posedge clk) disable iff (reset) !$fell(error_out)
    );

    // With no control inputs asserted, all outputs hold their values.
    outputs_stable_when_fully_idle: assert property (
        @(posedge clk) disable iff (reset)
            (!valid_in && !control_tag_in && !dequeue_in && !error_in && !por_req_in)
            |-> $stable({data_out, ecc_out, tag_out, valid_out, control_tag_out, error_out, dequeue_out, por_req_out})
    );
endmodule