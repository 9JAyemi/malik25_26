module a_assertions #(parameter BITS = 32) (
    input logic clock,
    input logic [BITS-1:0] a_in,
    input logic [BITS-1:0] b_in,
    input logic [BITS-1:0] out
);
    // Even a_in makes out capture b_in divided by two on the next cycle.
    check_even_selects_half: assert property (
        @(posedge clock) (a_in[0] == 1'b0) |=> (out == ($past(b_in) >> 1))
    );

    // Odd a_in makes out capture b_in multiplied by two on the next cycle.
    check_odd_selects_double: assert property (
        @(posedge clock) (a_in[0] == 1'b1) |=> (out == ($past(b_in) << 1))
    );

    // out always matches the transform selected by the previous cycle's a_in.
    check_out_matches_prior_inputs: assert property (
        @(posedge clock) 1'b1 |=> (out == ($past(a_in[0]) ? ($past(b_in) << 1) : ($past(b_in) >> 1)))
    );

    // Zero b_in produces zero out on the next cycle in either branch.
    check_zero_b_in_yields_zero: assert property (
        @(posedge clock) (b_in == '0) |=> (out == '0)
    );
endmodule

bind a a_assertions #(.BITS(BITS)) a_assertions_bind (
    .clock(clock),
    .a_in(a_in),
    .b_in(b_in),
    .out(out)
);

module b_assertions #(parameter BITS = 32) (
    input logic clock,
    input logic [BITS-1:0] a_in,
    input logic [BITS-1:0] b_in,
    input logic [BITS-1:0] temp,
    input logic [BITS-1:0] out
);
    // out captures the previous cycle's a_in XOR temp.
    check_out_registers_a_xor_temp: assert property (
        @(posedge clock) 1'b1 |=> (out == ($past(a_in) ^ $past(temp)))
    );

    // Zero temp makes out capture a_in unchanged on the next cycle.
    check_zero_temp_passthrough: assert property (
        @(posedge clock) (temp == '0) |=> (out == $past(a_in))
    );

    // Zero a_in makes out capture temp unchanged on the next cycle.
    check_zero_a_in_passthrough: assert property (
        @(posedge clock) (a_in == '0) |=> (out == $past(temp))
    );

    // Equal a_in and temp cancel through XOR on the next cycle.
    check_equal_inputs_cancel: assert property (
        @(posedge clock) (a_in == temp) |=> (out == '0)
    );
endmodule

bind b b_assertions #(.BITS(BITS)) b_assertions_bind (
    .clock(clock),
    .a_in(a_in),
    .b_in(b_in),
    .temp(temp),
    .out(out)
);