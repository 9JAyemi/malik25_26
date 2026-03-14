module d_flipflop_with_setreset(input D, SET_B, VPWR, VGND, VPB, VNB, CLK,
                                output Q, Q_N);

    // Internal signals
    wire S;
    wire R;

    // Set/reset circuitry
    assign S = ~SET_B & VPB & VNB;
    assign R = SET_B & VPB & VNB;

    // D latch
    reg Q_reg;
    always @(posedge CLK)
    begin
        if (S) Q_reg <= 1'b1;
        else if (R) Q_reg <= 1'b0;
        else Q_reg <= D;
    end

    // Output
    assign Q = Q_reg;
    assign Q_N = ~Q_reg;

endmodule