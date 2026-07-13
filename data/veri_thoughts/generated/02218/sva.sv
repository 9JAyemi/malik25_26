module subfxp_sva #(
    parameter int width = 16,
    parameter int cycles = 1
) (
    input  logic                         clk,
    input  logic signed [width-1:0]      a,
    input  logic signed [width-1:0]      b,
    input  logic signed [width-1:0]      q
);
    // Clock: clk. No reset in RTL.
    // Sequential pipeline: res[0] <= a-b; res[i] <= res[i-1] >> 1; q = res[cycles-1].
    // End-to-end behavior: q equals (a-b) delayed 'cycles' clocks and logically right-shifted by (cycles-1).

    localparam int SHIFT = (cycles > 0) ? (cycles - 1) : 0;

    // q matches the pipelined subtract and shift: q == $past(a-b, cycles) >> (cycles-1).
    check_end_to_end: assert property (
        @(posedge clk) $past(1'b1, cycles) |-> ( q == ($past(a - b, cycles) >> SHIFT) )
    );

    // If the past difference was zero, q must be zero after the pipeline latency.
    check_zero_diff_propagates_zero: assert property (
        @(posedge clk) ($past(1'b1, cycles) && ($past(a - b, cycles) == '0)) |-> (q == '0)
    );

    // If past b was zero, q equals past a logically right-shifted by (cycles-1).
    check_b_zero_passthrough: assert property (
        @(posedge clk) ($past(1'b1, cycles) && ($past(b, cycles) == '0)) |-> ( q == ($past(a, cycles) >> SHIFT) )
    );

    // If past a was zero, q equals negative past b logically right-shifted by (cycles-1).
    check_a_zero_negate: assert property (
        @(posedge clk) ($past(1'b1, cycles) && ($past(a, cycles) == '0)) |-> ( q == ((- $past(b, cycles)) >> SHIFT) )
    );

    // For cycles==1, stable inputs imply a stable output one cycle later (direct-register behavior).
    genvar _g;
    generate
        if (cycles == 1) begin : gen_c1_stability
            // With cycles==1, if a and b are stable, q is stable as well.
            check_stable_inputs_imply_stable_q_c1: assert property (
                @(posedge clk) ($stable(a) && $stable(b)) |-> $stable(q)
            );
        end
    endgenerate

    // For cycles>1 and SHIFT <= width, MSBs introduced by logical shift must be zero after latency.
    generate
        if (cycles > 1) begin : gen_shift_props
            if (SHIFT <= width) begin : gen_msb_zero
                // After latency, upper SHIFT bits of q are zero due to logical right shift.
                check_msb_zero_after_shift: assert property (
                    @(posedge clk) $past(1'b1, cycles) |-> ( q[width-1 -: SHIFT] == '0 )
                );
            end
            else begin : gen_shift_ge_width
                // If SHIFT >= width, the logical shift yields zero.
                check_full_shift_yields_zero: assert property (
                    @(posedge clk) $past(1'b1, cycles) |-> ( q == '0 )
                );
            end
        end
    endgenerate

endmodule