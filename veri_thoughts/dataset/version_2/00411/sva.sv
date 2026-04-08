module lfsr_counter_assertions #(
    parameter SIZE = 4
)(
    input logic clk,
    input logic reset,
    input logic ena,
    input logic [SIZE-1:0] out
);

    // A sampled low reset keeps the next sampled output at zero.
    check_reset_clears_out: assert property (
        @(posedge clk) !reset |=> (out == '0)
    );

    // When disabled, the state holds its previous value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (!reset)
        !ena |=> (out == $past(out))
    );

    generate
        if (SIZE > 1) begin : gen_lfsr_checks
            // When enabled, the upper bits shift in the previous lower bits.
            check_shift_when_enabled: assert property (
                @(posedge clk) disable iff (!reset)
                ena |=> (out[SIZE-1:1] == $past(out[SIZE-2:0]))
            );

            // When enabled, the new LSB is the XOR of the previous top two bits.
            check_feedback_when_enabled: assert property (
                @(posedge clk) disable iff (!reset)
                ena |=> (out[0] == ($past(out[SIZE-1]) ^ $past(out[SIZE-2])))
            );
        end
    endgenerate

endmodule