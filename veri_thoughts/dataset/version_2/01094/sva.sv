module parity_sva #(
    parameter n = 8
)(
    input logic [n-1:0] in,
    input logic parity_out,
    input logic error_flag
);

    ///// Functional relations /////
    // On parity_out rising, outputs reflect parity_out=~in[n-1] and error_flag=in[n-1].
    check_parity_rise_function: assert property (
        @(posedge parity_out) (parity_out == ~in[n-1]) && (error_flag == in[n-1])
    );

    // On error_flag rising, outputs reflect parity_out=~in[n-1] and error_flag=in[n-1].
    check_error_rise_function: assert property (
        @(posedge error_flag) (parity_out == ~in[n-1]) && (error_flag == in[n-1])
    );

    // On MSB rising, outputs reflect parity_out=~in[n-1] and error_flag=in[n-1].
    check_msb_rise_function: assert property (
        @(posedge in[n-1]) (parity_out == ~in[n-1]) && (error_flag == in[n-1])
    );

    // On parity_out rising, error_flag must be LOW (outputs are complements).
    check_complement_on_parity_rise: assert property (
        @(posedge parity_out) (error_flag == 1'b0)
    );

    // On error_flag rising, parity_out must be LOW (outputs are complements).
    check_complement_on_error_rise: assert property (
        @(posedge error_flag) (parity_out == 1'b0)
    );

    // On parity_out rising, MSB must be LOW (since parity_out = ~in[n-1]).
    check_parity_rise_implies_msb_low: assert property (
        @(posedge parity_out) (in[n-1] == 1'b0)
    );

    // On error_flag rising, MSB must be HIGH (since error_flag = in[n-1]).
    check_error_rise_implies_msb_high: assert property (
        @(posedge error_flag) (in[n-1] == 1'b1)
    );

    ///// Independence from lower bits /////
    // Any low-order bit rising alone must not change outputs (MSB stable).
    if (n > 1) begin : gen_lower_independence
        genvar i;
        for (i = 0; i < n-1; i++) begin : g_no_influence
            lower_bit_rise_no_output_change: assert property (
                @(posedge in[i]) $stable(in[n-1]) |-> $stable(parity_out) && $stable(error_flag)
            );
        end
    end

endmodule