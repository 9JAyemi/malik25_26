module mux_16to1_sva (
    input logic [3:0] s,
    input logic i15, i14, i13, i12, i11, i10, i9, i8,
    input logic i7, i6, i5, i4, i3, i2, i1, i0,
    input logic z
);

    // No RTL clock or reset; sample the combinational mux on the formal global clock.

    // s=0 selects i0.
    check_select_i0: assert property (
        @($global_clock) (s === 4'h0) |-> (z === i0)
    );

    // s=1 selects i1.
    check_select_i1: assert property (
        @($global_clock) (s === 4'h1) |-> (z === i1)
    );

    // s=2 selects i2.
    check_select_i2: assert property (
        @($global_clock) (s === 4'h2) |-> (z === i2)
    );

    // s=3 selects i3.
    check_select_i3: assert property (
        @($global_clock) (s === 4'h3) |-> (z === i3)
    );

    // s=4 selects i4.
    check_select_i4: assert property (
        @($global_clock) (s === 4'h4) |-> (z === i4)
    );

    // s=5 selects i5.
    check_select_i5: assert property (
        @($global_clock) (s === 4'h5) |-> (z === i5)
    );

    // s=6 selects i6.
    check_select_i6: assert property (
        @($global_clock) (s === 4'h6) |-> (z === i6)
    );

    // s=7 selects i7.
    check_select_i7: assert property (
        @($global_clock) (s === 4'h7) |-> (z === i7)
    );

    // s=8 selects i8.
    check_select_i8: assert property (
        @($global_clock) (s === 4'h8) |-> (z === i8)
    );

    // s=9 selects i9.
    check_select_i9: assert property (
        @($global_clock) (s === 4'h9) |-> (z === i9)
    );

    // s=A selects i10.
    check_select_i10: assert property (
        @($global_clock) (s === 4'hA) |-> (z === i10)
    );

    // s=B selects i11.
    check_select_i11: assert property (
        @($global_clock) (s === 4'hB) |-> (z === i11)
    );

    // s=C selects i12.
    check_select_i12: assert property (
        @($global_clock) (s === 4'hC) |-> (z === i12)
    );

    // s=D selects i13.
    check_select_i13: assert property (
        @($global_clock) (s === 4'hD) |-> (z === i13)
    );

    // s=E selects i14.
    check_select_i14: assert property (
        @($global_clock) (s === 4'hE) |-> (z === i14)
    );

    // s=F selects i15.
    check_select_i15: assert property (
        @($global_clock) (s === 4'hF) |-> (z === i15)
    );

    // Non-binary select values drive the default output low.
    check_default_output_low: assert property (
        @($global_clock)
        ((s !== 4'h0) && (s !== 4'h1) && (s !== 4'h2) && (s !== 4'h3) &&
         (s !== 4'h4) && (s !== 4'h5) && (s !== 4'h6) && (s !== 4'h7) &&
         (s !== 4'h8) && (s !== 4'h9) && (s !== 4'hA) && (s !== 4'hB) &&
         (s !== 4'hC) && (s !== 4'hD) && (s !== 4'hE) && (s !== 4'hF))
        |-> (z === 1'b0)
    );

endmodule