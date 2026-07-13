module johnson_counter_sva #(
    parameter int m = 4
) (
    input logic clk,
    input logic [m-1:0] out
);

generate
    if (m > 1) begin : gen_multi_bit
        // Output is a one-bit circular shift of its previous value.
        check_rotate_vector: assert property (
            @(posedge clk) !$initstate |-> (out == {$past(out[m-2:0]), $past(out[m-1])})
        );

        // The low bit comes from the previous high bit.
        check_wrap_bit: assert property (
            @(posedge clk) !$initstate |-> (out[0] == $past(out[m-1]))
        );

        // Upper bits come from the previous lower bits.
        check_shift_upper_bits: assert property (
            @(posedge clk) !$initstate |-> (out[m-1:1] == $past(out[m-2:0]))
        );
    end else begin : gen_single_bit
        // A 1-bit instance holds its value on each clock.
        check_single_bit_hold: assert property (
            @(posedge clk) !$initstate |-> (out == $past(out))
        );
    end
endgenerate

// Bit parity is preserved by the circular shift.
check_parity_preserved: assert property (
    @(posedge clk) !$initstate |-> ((^out) == (^($past(out))))
);

// The all-zero state remains all zero.
check_zero_state_stable: assert property (
    @(posedge clk) (!$initstate && ($past(out) == {m{1'b0}})) |-> (out == {m{1'b0}})
);

// The all-one state remains all one.
check_one_state_stable: assert property (
    @(posedge clk) (!$initstate && ($past(out) == {m{1'b1}})) |-> (out == {m{1'b1}})
);

endmodule