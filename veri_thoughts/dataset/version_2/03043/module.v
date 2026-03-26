module myDFFSR (
    input D, 
    input C, 
    input R, 
    input S, 
    output Q
    );

    reg Q;

    always @(posedge C) begin
        if (R) begin
            Q <= 0;
        end else if (S) begin
            Q <= 1;
        end else begin
            Q <= D;
        end
    end

endmodule