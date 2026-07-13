
module and1_fixed (output o, input i0, i1, i2, i3, i4, i5);
    assign o = i0 & i1 & i2 & i3 & i4 & i5;
endmodule

module and2_fixed (output o, input i0, i1, i2, i3, i4, i5);
    assign o = i0 & i1 & i2 & i3 & i4 & i5;
endmodule

module and_or_gate_fixed (output o, input i0, i1, i2, i3, i4, i5);
    wire w1;

    and1_fixed and1 (w1, i0, i1, i2, i3, i4, i5);
    and2_fixed and2 (o, w1, w1, w1, w1, w1, w1);
endmodule
