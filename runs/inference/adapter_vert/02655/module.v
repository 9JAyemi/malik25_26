module or4 (
    output reg X,
    input wire A,
    input wire B,
    input wire C,
    input wire D
);

    always @ (A or B or C or D) begin
        X <= A | B | C | D;
    end

endmodule

module or4_2_custom (
    output reg X,
    input wire A,
    input wire B,
    input wire C,
    input wire D,
    input wire VPWR,
    input wire VGND,
    input wire VPB,
    input wire VNB
);

    wire or_output;
    
    or4 or4_inst (
        .X(or_output),
        .A(A),
        .B(B),
        .C(C),
        .D(D)
    );
    
    always @* begin
        X <= or_output;
    end

endmodule