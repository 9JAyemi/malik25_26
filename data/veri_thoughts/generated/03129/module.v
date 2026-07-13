module and4_4 (
    output X,
    input A,
    input B,
    input C,
    input D
);

    // Voltage supply signals
    supply0 VPWR;
    supply0 VGND;
    supply0 VPB ;
    supply0 VNB ;

    and base (
        X,
        A,
        B,
        C,
        D
    );

endmodule