module bitwise_or_sva (
    input logic        clock,
    input logic [7:0]  a_in,
    input logic [7:0]  b_in,
    input logic [7:0]  out
);

    // Output is the registered OR of the prior cycle inputs.
    check_registered_or: assert property (
        @(posedge clock) disable iff ($initstate)
        out == ($past(a_in) | $past(b_in))
    );

    // A zero a input passes b through on the next cycle.
    check_zero_a_passthrough: assert property (
        @(posedge clock) disable iff ($initstate)
        (a_in == 8'h00) |=> (out == $past(b_in))
    );

    // A zero b input passes a through on the next cycle.
    check_zero_b_passthrough: assert property (
        @(posedge clock) disable iff ($initstate)
        (b_in == 8'h00) |=> (out == $past(a_in))
    );

    // All ones on a forces all ones on the next cycle.
    check_all_ones_a: assert property (
        @(posedge clock) disable iff ($initstate)
        (a_in == 8'hFF) |=> (out == 8'hFF)
    );

    // All ones on b forces all ones on the next cycle.
    check_all_ones_b: assert property (
        @(posedge clock) disable iff ($initstate)
        (b_in == 8'hFF) |=> (out == 8'hFF)
    );

    // If both inputs are zero, the output is zero on the next cycle.
    check_zero_inputs_zero_output: assert property (
        @(posedge clock) disable iff ($initstate)
        ((a_in == 8'h00) && (b_in == 8'h00)) |=> (out == 8'h00)
    );

    // If both inputs are all ones, the output is all ones on the next cycle.
    check_all_ones_inputs_all_ones_output: assert property (
        @(posedge clock) disable iff ($initstate)
        ((a_in == 8'hFF) && (b_in == 8'hFF)) |=> (out == 8'hFF)
    );

endmodule