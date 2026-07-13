
module TLATNTSCAX2TS (D, E, SE, CK, Q);
    input D, E, SE, CK;
    output Q;

    reg Q;

    always @(posedge CK) begin
        if (E && SE) begin
            Q <= D;
        end
    end
endmodule

module BUFX3TS (A, OE, Y);
    input A, OE;
    output Y;

    assign Y = OE ? A : 1'b0;
endmodule
