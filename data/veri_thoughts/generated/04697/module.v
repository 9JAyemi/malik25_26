module and_4 (
    output Y,
    input A,
    input B,
    input C,
    input D,
    input VPWR,
    input VGND,
    input VPB,
    input VNB
);

    wire tmp1, tmp2;
    
    and and2_1 (
        tmp1,
        A,
        B
    );
    
    and and2_2 (
        tmp2,
        C,
        D
    );
    
    and and2_3 (
        Y,
        tmp1,
        tmp2
    );

endmodule