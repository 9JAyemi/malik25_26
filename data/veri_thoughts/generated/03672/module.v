
module five_to_one (
    X,
    A1,
    A2,
    B1,
    C1,
    D1
);

    output reg X ;
    input  A1;
    input  A2;
    input  B1;
    input  C1;
    input  D1;

    // Voltage supply signals
    supply1 VPWR;
    supply0 VGND;
    supply1 VPB ;
    supply0 VNB ;

    always @ ( A1 or A2 or B1 or C1 or D1 ) begin
        if (D1) 
            X <= (A1 & A2) | (B1 & ~C1);
        else 
            X <= 0;
    end

endmodule