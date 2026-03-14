module original_gate_sva (
    input logic        clk,
    input logic [4:0]  ctrl,
    input logic [1:0]  din,
    input logic [0:0]  sel,
    input logic [31:0] dout
);
    // No reset in RTL; all checks are synchronous to clk.

    // Case 0 writes entire dout: low bits from din.
    case0_write_lowbits: assert property (
        @(posedge clk) ((sel == 1'b0) || (ctrl == 5'd0)) |-> (dout[1:0] == din)
    );

    // Case 0 zeroes the upper bits [31:2].
    case0_zero_upper: assert property (
        @(posedge clk) ((sel == 1'b0) || (ctrl == 5'd0)) |-> (dout[31:2] == '0)
    );

    // For k=1..30: dout[k] gets din[0], dout[k+1] gets din[1].
    genvar k;
    generate
        for (k = 1; k <= 30; k++) begin : g_map_data
            // In case k, dout[k] captures din[0].
            map_bit0: assert property (
                @(posedge clk) (sel == 1'b1 && ctrl == k) |-> (dout[k] == din[0])
            );
            // In case k, dout[k+1] captures din[1].
            map_bit1: assert property (
                @(posedge clk) (sel == 1'b1 && ctrl == k) |-> (dout[k+1] == din[1])
            );
        end
    endgenerate

    // Case 31 writes only dout[31] with din[0] (width truncation).
    case31_bit0: assert property (
        @(posedge clk) (sel == 1'b1 && ctrl == 5'd31) |-> (dout[31] == din[0])
    );

    // For k=1..29: bits above k+1 are zeroed.
    genvar ku;
    generate
        for (ku = 1; ku <= 29; ku++) begin : g_zero_upper
            // In case k, bits [31:k+2] are driven to zero.
            zero_upper: assert property (
                @(posedge clk) (sel == 1'b1 && ctrl == ku) |-> (dout[31:ku+2] == '0)
            );
        end
    endgenerate

    // For k=1..31: lower bits [k-1:0] hold previous value.
    genvar kh;
    generate
        for (kh = 1; kh <= 31; kh++) begin : g_hold_lower
            // In case k, lower bits below k retain prior value.
            hold_lower: assert property (
                @(posedge clk) $past(1'b1) && (sel == 1'b1 && ctrl == kh) |-> (dout[kh-1:0] == $past(dout[kh-1:0]))
            );
        end
    endgenerate
endmodule