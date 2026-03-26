module acl_fp_extract_exp_sva #(
    parameter WIDTH = 32,
    parameter HIGH_CAPACITY = 1
) (
    input logic clock,
    input logic resetn,
    input logic enable,
    input logic valid_in,
    input logic valid_out,
    input logic stall_in,
    input logic stall_out,
    input logic [WIDTH-1:0] dataa,
    input logic [31:0] result
);

    // During reset, valid_out is cleared.
    reset_clears_valid: assert property (
        @(posedge clock) !resetn |-> (valid_out === 1'b0)
    );

    // During reset, stall_out is low because the stage is invalid.
    reset_clears_stall: assert property (
        @(posedge clock) !resetn |-> (stall_out === 1'b0)
    );

    // stall_out is the AND of valid_out and stall_in.
    check_stall_out_equation: assert property (
        @(posedge clock) disable iff (!resetn)
        (stall_out === (valid_out & stall_in))
    );

    generate
        if (HIGH_CAPACITY == 1) begin : gen_high_capacity
            // A full stalled stage holds valid_out.
            hold_valid_on_stall: assert property (
                @(posedge clock) disable iff (!resetn)
                ((valid_out === 1'b1) && (stall_in === 1'b1)) |=> (valid_out === $past(valid_out))
            );

            // A full stalled stage holds result.
            hold_result_on_stall: assert property (
                @(posedge clock) disable iff (!resetn)
                ((valid_out === 1'b1) && (stall_in === 1'b1)) |=> (result === $past(result))
            );

            // When not blocked, valid_out captures valid_in.
            capture_valid_high_capacity: assert property (
                @(posedge clock) disable iff (!resetn)
                ((valid_out === 1'b0) || (stall_in === 1'b0)) |=> (valid_out === $past(valid_in))
            );
        end else begin : gen_low_capacity
            // When enable is low, valid_out holds.
            hold_valid_when_disabled: assert property (
                @(posedge clock) disable iff (!resetn)
                (enable === 1'b0) |=> (valid_out === $past(valid_out))
            );

            // When enable is low, result holds.
            hold_result_when_disabled: assert property (
                @(posedge clock) disable iff (!resetn)
                (enable === 1'b0) |=> (result === $past(result))
            );

            // When enable is high, valid_out captures valid_in.
            capture_valid_low_capacity: assert property (
                @(posedge clock) disable iff (!resetn)
                (enable === 1'b1) |=> (valid_out === $past(valid_in))
            );
        end
    endgenerate

    generate
        if (WIDTH == 32) begin : gen_width32
            if (HIGH_CAPACITY == 1) begin : gen_width32_high_capacity
                // Enabled zero or all-one exponent maps to 0x7fffffff.
                capture_special_exponent_32_high_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    (((valid_out === 1'b0) || (stall_in === 1'b0)) &&
                     ((~(|dataa[WIDTH-2:WIDTH-9])) || (&dataa[WIDTH-2:WIDTH-9])))
                    |=> (result === 32'h7fffffff)
                );

                // Enabled normal exponent is unbiased by 127.
                capture_normal_exponent_32_high_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    (((valid_out === 1'b0) || (stall_in === 1'b0)) &&
                     (|dataa[WIDTH-2:WIDTH-9]) &&
                     ~(&dataa[WIDTH-2:WIDTH-9]))
                    |=> (result === {{23{1'b0}}, $past((({1'b0, dataa[WIDTH-2:WIDTH-9]}) - 9'd127))})
                );
            end else begin : gen_width32_low_capacity
                // Enabled zero or all-one exponent maps to 0x7fffffff.
                capture_special_exponent_32_low_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    ((enable === 1'b1) &&
                     ((~(|dataa[WIDTH-2:WIDTH-9])) || (&dataa[WIDTH-2:WIDTH-9])))
                    |=> (result === 32'h7fffffff)
                );

                // Enabled normal exponent is unbiased by 127.
                capture_normal_exponent_32_low_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    ((enable === 1'b1) &&
                     (|dataa[WIDTH-2:WIDTH-9]) &&
                     ~(&dataa[WIDTH-2:WIDTH-9]))
                    |=> (result === {{23{1'b0}}, $past((({1'b0, dataa[WIDTH-2:WIDTH-9]}) - 9'd127))})
                );
            end
        end else begin : gen_width_other
            if (HIGH_CAPACITY == 1) begin : gen_width_other_high_capacity
                // Enabled zero or all-one exponent maps to 0x7fffffff.
                capture_special_exponent_other_high_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    (((valid_out === 1'b0) || (stall_in === 1'b0)) &&
                     ((~(|dataa[WIDTH-2:WIDTH-12])) || (&dataa[WIDTH-2:WIDTH-12])))
                    |=> (result === 32'h7fffffff)
                );

                // Enabled normal exponent is unbiased by 1023.
                capture_normal_exponent_other_high_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    (((valid_out === 1'b0) || (stall_in === 1'b0)) &&
                     (|dataa[WIDTH-2:WIDTH-12]) &&
                     ~(&dataa[WIDTH-2:WIDTH-12]))
                    |=> (result === {{20{1'b0}}, $past((({1'b0, dataa[WIDTH-2:WIDTH-12]}) - 12'd1023))})
                );
            end else begin : gen_width_other_low_capacity
                // Enabled zero or all-one exponent maps to 0x7fffffff.
                capture_special_exponent_other_low_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    ((enable === 1'b1) &&
                     ((~(|dataa[WIDTH-2:WIDTH-12])) || (&dataa[WIDTH-2:WIDTH-12])))
                    |=> (result === 32'h7fffffff)
                );

                // Enabled normal exponent is unbiased by 1023.
                capture_normal_exponent_other_low_capacity: assert property (
                    @(posedge clock) disable iff (!resetn)
                    ((enable === 1'b1) &&
                     (|dataa[WIDTH-2:WIDTH-12]) &&
                     ~(&dataa[WIDTH-2:WIDTH-12]))
                    |=> (result === {{20{1'b0}}, $past((({1'b0, dataa[WIDTH-2:WIDTH-12]}) - 12'd1023))})
                );
            end
        end
    endgenerate

endmodule