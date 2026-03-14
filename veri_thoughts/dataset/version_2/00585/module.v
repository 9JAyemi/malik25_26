module mux_2to1 (
    input A,
    input B,
    input S,
    output reg Y
);

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    always @* begin
        if (S == 0)
            Y = A;
        else
            Y = B;
    end

endmodule