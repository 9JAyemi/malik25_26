module input_output_sva (
    input logic        clk,
    input logic [6:0]  a,
    input logic        a_msb,
    input logic [14:0] b,
    input logic        b_msb
);

    // b[0] is a_msb gated by the stored LSB carried on b[1].
    check_b_lsb_gate: assert property (
        @(posedge clk) b[0] == (a_msb & b[1])
    );

    // With a_msb low, the observable accumulator slice adds zero-extended a.
    check_slice_update_no_extend: assert property (
        @(posedge clk) (!a_msb) |=> (b[14:1] == ($past(b[14:1]) + {7'h00, $past(a)}))
    );

    // With a_msb high, the observable accumulator slice adds {7'h7F, a}.
    check_slice_update_with_extend: assert property (
        @(posedge clk) (a_msb) |=> (b[14:1] == ($past(b[14:1]) + {7'h7F, $past(a)}))
    );

    // The stored bit0, exposed on b[1], updates with the previous a[0].
    check_state_bit0_update: assert property (
        @(posedge clk) 1'b1 |=> (b[1] == ($past(b[1]) ^ $past(a[0])))
    );

    // A non-extended add without low-14 overflow leaves b_msb unchanged.
    check_b_msb_hold_without_low14_carry: assert property (
        @(posedge clk) ((!a_msb) && (({1'b0, b[14:1]} + {8'h00, a}) < 15'h4000)) |=> (b_msb == $past(b_msb))
    );

endmodule