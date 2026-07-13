module and_gate(
    input A,
    input B,
    output X
);

    wire A1, A2, B1, C1, VPWR, VGND, VPB, VNB;
    assign A1 = A;
    assign B1 = B;
    assign A2 = 1'b1;
    assign C1 = 1'b0;
    assign VPWR = 1'b1;
    assign VGND = 1'b0;
    assign VPB = 1'b1;
    assign VNB = 1'b0;
    
    and gate_inst (
        X,
        A1,
        B1
    );

endmodule